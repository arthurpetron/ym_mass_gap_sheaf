# Original-action bounded-degree sweep energy and coordinate covariance

## Result

Let A be the constructed eight-layer sweep of ALL physical links and let
R_i=I-C_i, where C_i is the existing original full-action conditional
projection. On the SAME completed weighted GNS carrier, the new proof gives

    sum_i ||R_i A x||^2 <= 625 (||x||^2 - ||A x||^2).

The coefficient is 25 squared, from the explicit row AND column Ward-star
incidence bounds. It does not depend on nome, representation cutoff or finite
extent. The theorem holds for the existing positive original actions with
0<w<1 and K>=headCutoff(w), with no centered-sector or gap premise.

This is an UPPER residual-energy bound. It is not the missing positive LOWER
coercivity bound, and does not itself give contraction below one.

In parallel, the same normalized covariance/sweep equality now has a
coordinate-distance hypothesis: root distance greater than 8*rounds plus
the two actual probe-carrier sizes guarantees cone/test separation. Heat
cutoff stage and conditional sweep rounds remain separate parameters.

## Exact causal proof

1. On the existing completion, the finite Gram identity writes
   `n*sum ||v_i||^2 - ||sum v_i||^2` as the sum of all unordered squared
   differences. Nonnegativity gives the sharp finite-sum norm bound without
   square roots, choice of representatives, or dimension assumptions.
2. After link i's own update, its residual is zero. A nonneighbor update
   transports every current correction vector by its actual contractive
   projection. A neighbor adds the negative actual correction
   `-R_i R_j x_previous`. This constructs an exact sparse representation,
   including every later nonneighbor transport.
3. The correction list has exactly the later-neighbor count. Its total
   energy is at most the sum of the actual neighboring step losses. The
   Gram bound costs at most 25 for the row.
4. Earlier losses are discarded only by nonnegativity. Summing the rows
   charges each actual intermediate step loss at most 25 times, by the
   transpose incidence bound. No ambient-volume factor is introduced.
5. The existing exact Pythagorean telescope identifies the sum of these
   losses with `||x||^2-||Ax||^2`.

| Declaration | Source | Role |
|---|---|---|
| `energy_deficit` | `lean/YMGap/Continuum/GNSFiniteSumEnergy.lean:189` | Exact completed Gram identity. |
| `norm_vectorSum_le_of_length` | `lean/YMGap/Continuum/GNSFiniteSumEnergy.lean:209` | Finite-vector estimate with the supplied geometric count. |
| `correctionWalk` | `lean/YMGap/Continuum/GNSProjectionSweepSparseRow.lean:99` | Explicit signed, transported correction list. |
| `correctionWalk_eq` | `lean/YMGap/Continuum/GNSProjectionSweepSparseRow.lean:118` | Exact final-residual representation. |
| `correctionWalk_length` | `lean/YMGap/Continuum/GNSProjectionSweepSparseRow.lean:137` | Counts precisely the neighboring insertions. |
| `correctionWalk_energy` | `lean/YMGap/Continuum/GNSProjectionSweepSparseRow.lean:152` | Charges only actual intermediate losses. |
| `after_own_row_bound` | `lean/YMGap/Continuum/GNSProjectionSweepSparseRow.lean:180` | Sparse bound after the row's own update. |
| `row_bound_of_mem` | `lean/YMGap/Continuum/GNSProjectionSweepEnergy.lean:142` | Full-trajectory row bound with nonnegative earlier losses. |
| `neighborLoss_sum_le` | `lean/YMGap/Continuum/GNSProjectionSweepEnergy.lean:160` | Counts transpose incidence against actual step losses. |
| `finalEnergy_le_norm_loss` | `lean/YMGap/Continuum/GNSProjectionSweepEnergy.lean:204` | Generic g-squared completed energy estimate. |
| `column_count` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:35` | Physical transpose count from symmetric literal adjacency. |
| `nonadjacent_commute` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:60` | Same original conditional operators. |
| `final_energy_le_625_loss` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:71` | Concrete physical estimate for any duplicate-free physical schedule. |
| `eight_layer_energy_le_625_loss` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:84` | Constructed schedule includes ALL physical links. |
| `near_coordinate` | `lean/YMGap/Continuum/BF4ExactSlabConeCoordinateDistance.lean:47` | One star step changes each coordinate by at most one. |
| `grow_coordinate` | `lean/YMGap/Continuum/BF4ExactSlabConeCoordinateDistance.lean:61` | Iterated cone bound from an original support link. |
| `contact_root_bound` | `lean/YMGap/Continuum/BF4ExactSlabConeCoordinateDistance.lean:81` | Literal probe-carrier roots bound cone contact. |
| `covariance_as_sweep_pairing_of_root_far` | `lean/YMGap/Continuum/BF4ExactSlabConeCoordinateDistance.lean:137` | Coordinate separation feeds the original normalized covariance identity. |

The complete physical schedule's coverage and uniqueness are the existing
`schedule_covers` and `schedule_nodup` in
`lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:65` and `:85`.
All vectors and norms retain `fullData hw0 hw1 K extent hK`. No free-Haar
measure, surrogate carrier, OS transfer or physical Hamiltonian is substituted.

## Refined next mathematical task

The bounded-degree upper estimate is no longer an open input. The remaining
analytic task is a useful positive lower bound for the SAME original-action
Dirichlet energy on the actual unit-centered states, with explicit dependence
on nome, cutoff, extent and a justified physical scaling family.

In particular, if a direct lower bound `delta*||y||^2 <= sum_i||R_i y||^2`
is proved for unit-centered completed y, the already checked unit fixation
and centering preservation permit its use at y=Ax. The new upper bound then
gives `(625+delta)*||Ax||^2 <=625*||x||^2`. This paragraph records the
mathematical next argument, not a new Lean contraction declaration: no such
useful lower bound is supplied by this increment.

On that direct centered route, a separate identification of the entire joint
fixed space with constants is NOT an independent prerequisite. It remains
unproved, and is still required if using a lower bound restricted only to
the abstract common-fixed complement. Do not impose that stronger detour
before attempting the directly sufficient centered inequality.

The generic projection/Gram argument is group-agnostic. Its uniform upper
constant does not assert a uniform positive lower constant for any group.
In particular it supplies no abelian or nonabelian mass-gap conclusion. The
physical instance here remains the existing SU(2) action. Useful scaling,
nontrivial continuum survival, reflected OS reconstruction, physical mass,
full QFT axioms and every-group Clay closure remain open.

## Verification and review

Five focused monitored checks passed with one worker and a 20 GiB worker cap:
6 Gram gates, 8 sparse-row gates, 8 total-energy gates, 4 physical gates, and
5 geometry/covariance gates. All 31 printed dependencies are within
`{propext, Quot.sound}`; the final checks have no errors or warnings.
No full-tree build or audit was run. No source `sorry`, new axiom, analytic
field, canonical frontier edit or chart-marker change was introduced.

Initial checks found finite syntax/base-case, section-variable inclusion,
rewrite targeting and explicit-parameter errors; the mathematical statements
were retained. Sol developed the coordinate module and independently reviewed
the Gram identity, signed transports, row/column counting, actual physical
instance, and distinction between upper energy and missing lower coercivity.
The direct-centered strategy refinement above reflects that review. No new
routine math-ph listing scan was performed.
