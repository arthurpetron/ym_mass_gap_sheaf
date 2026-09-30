# Original cross-exterior replacement and conditional energy

## Whole-project goal and scope

The unchanged goal remains OPEN: constructive continuum Yang--Mills on R^4
for every compact simple group, with SAME-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian mass gap.

This checkpoint concerns the original finite-cutoff SU(2) slab weight at
0<w<1, K>=headCutoff(w), and an actual physical link j of that slab.
The conditional residual belongs to ordinary original-action weighted L2;
it is NOT OS time or the physical Hamiltonian.

Write n for the number of original link blocks, A for the incident action,
B for the entire complementary action, W=A*B for the full original action,
D=project_j A for its in-place normalizer, E for D at the other exterior,
and G_k for the finite reciprocal of D. Let S exchange just block j between
the two copies; A' instead exchanges every exterior block while retaining j.
Set ell=headFloor(w)^d, U=prefixCap(w)^d, rho=1-ell/U, where d is the
actual incident-face count. All dependence on the nome remains explicit.

## One denominator correction suffices

The checked raw certificate is U^2*A*E-ell^2*A'*D>=0. Multiplying it by
G_k and adding ell^2*A'*(D*G_k-(1-rho^k)) gives

    ell^2 (1-rho^k) A' <= U^2 A G_k E.

The second denominator E remains a literal polynomial. No reciprocal of E
and no second geometric-error factor are needed. The certificate and its
weighted Haar consequence are
`QuaternionHaarOneSidedReciprocalComparison.oneSidedCertificate` at
`lean/YMGap/Continuum/QuaternionHaarOneSidedReciprocalComparison.lean:52`
and `weighted_one_sided_comparison` at the same path, line99.
The actual slab instantiation is
`BF4ExactSlabOneSidedStarComparison.weighted_one_sided_star_comparison` at
`lean/YMGap/Continuum/BF4ExactSlabOneSidedStarComparison.lean:53`.

## Exact joins, not assumed kernel identifications

Let delta=S(f)-f, Z=H_n[W] and I_j=H_2n[W(x)W(y)*delta^2]. The insertion
in the one-sided comparison is

    r = S(W) * lift(B) * delta^2.

The first factor is S(W), NOT the unswapped first-copy W. Its positivity
is built from the original heat certificates and the actual square.

Paths below start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Exact content |
| --- | --- | --- |
| `singleton_pair_square_haar` | `SU2QuaternionCrossExteriorPair.lean:153` | Singleton Haar exchange recodes the original full pair to S(W)*A'*lift(B); delta^2 is invariant |
| `replacement_integral_pin` | `BF4ExactSlabCrossExteriorReplacement.lean:70` | I_j equals H[A'*r] on the original doubled carrier |
| `replacementInsertion_certificate` | `BF4ExactSlabCrossExteriorReplacement.lean:92` | Actual positive joint insertion, with no independent-face assumption |
| `comparison_integrand_pin` | `BF4ExactSlabCrossExteriorEnergyFubini.lean:98` | A*G_k*E*r becomes (B*G_k)*same-exterior replica energy*lift(B*D) |
| `singleton_conditional_replica_marginal` | `SU2QuaternionConditionalReplicaMarginal.lean:176` | The unused upper exterior factors by proved block disjointness; the first exterior stays inside the determinant |
| `reciprocal_independent` | `SU2QuaternionConditionalReplicaMarginal.lean:58` | Every finite reciprocal preserves the normalizer's termwise independence of j |
| `second_exterior_partition_pin` | `BF4ExactSlabCrossExteriorEnergyFubini.lean:132` | H_n[B*D]=Z, the original full partition, not its square |
| `covariance_head_pin` | `BF4ExactSlabInPlaceVarianceEnergy.lean:89` | Original singleton conditional moments equal the previously defined head-coordinate variance numerator |
| `inPlaceCovariance_energy_pin` | `BF4ExactSlabInPlaceVarianceEnergy.lean:151` | Retaining B and G_k gives the existing finite varianceEnergy |
| `comparison_integral_energy_pin` | `BF4ExactSlabCrossExteriorEnergyFubini.lean:170` | H[A*G_k*E*r]=Z*replicaIntegral_k, with the literal existing two-head integral |
| `original_replacement_finite_energy_bound` | `BF4ExactSlabCrossExteriorEnergyFubini.lean:189` | ell^2(1-rho^k) I_j <= U^2 Z replicaIntegral_k |

The existing replica integral equals twice finite varianceEnergy and has
already been identified at its CReal limit with twice the SAME conditional
residual squared norm. The factor two is not inserted into the partition
or silently lost in the two-copy change of variables.

## Actual conditional-energy limit

`GeometricCorrectedLimitOrder.correctionCutoff` in
`lean/YMGap/Continuum/GeometricCorrectedLimitOrder.lean:30` retains the
explicit geometricCutoff(rho,c*I,epsilon). The theorem
`geometric_corrected_limit_order` at the same path, line35, removes the
single finite correction using that cutoff and supplied Type-level
QCauchy data for the actual right-hand stream. It handles zero rate and
zero initial mass without division by either.

The slab consumer is
`BF4ExactSlabReplacementEnergyBound.original_replacement_energy_bound` in
`lean/YMGap/Continuum/BF4ExactSlabReplacementEnergyBound.lean:65`:

    ell^2 I_j <= U^2 Z * (energy_j + energy_j),

in CReal quotient order, where energy_j is exactly
`normSq ((projections ...).residual j (embedV fullData p))`.
The replica stream and its modulus are the previously constructed
`replicaIntegral` and `replicaCauchy`; its limit is rewritten using the
checked `replica_limit_eq_twice_residual_norm`. No new inverse, measure,
conditional projection, analytic estimate or assumed equality is supplied.
The statement ranges over supported original polynomials embedded in the
completion, not an unproved integral for arbitrary completed inputs.

## Remaining scope

This is a local replacement comparison, not a completed finite-volume
Poincare inequality or a physical gap. Joining and summing all path terms,
and pinning their order to the proved time-layer cut geometry, are separate
tasks. The raw coordinate prefix and the eight-color conditional schedule
are not asserted to be chronological. The candidate
n*(prefixCap/headFloor)^(2C+12) remains unproved as a global inequality;
even that candidate's area-dependent loss would not give useful signed
spatial/scaling control. No cutoff/spatial/spacing passage, continuum
survival, full QFT, finite physical mass or every-group closure is claimed.

The reviewed next geometric construction is to concatenate, for each
time t=0,...,extent, the original block indices whose physical link has
time t. Existing membership/time-admissibility facts are
`correctedSlabLinkAt_mem` in
`lean/YMGap/Continuum/BF4ExactSlabVacuumReflection.lean:100` and
`linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks` in
`lean/YMGap/Continuum/Z4HalfTimeReflectionGeometry.lean:485`.
Nodup, coverage and the earlier/later-time properties of every prefix
still have to be proved for this new ordering. The existing
`path_cauchy_certificate` in
`lean/YMGap/Continuum/SU2QuaternionReplicaPathTelescope.lean:88` accepts
an arbitrary supported polynomial path; `reindex_comp_cancel` in
`lean/YMGap/Continuum/SU2QuaternionDisjointPartialSwap.lean:186` supplies
the disjoint next-block composition. `crossingCount_le_area` in
`lean/YMGap/Continuum/BF4ExactSlabReplicaCutComparison.lean:63` already
permits arbitrary partial selection within the current time layer. These
are reusable proved inputs, NOT a checked chronological path theorem.

## Verification boundary

All nine modules passed focused serialized checks through the safe launcher,
one worker, 20 GiB worker ceiling, 12 GiB OS reserve, with automatic safety
telemetry intact. Every check completed during its initial call; there was
no live long-running compiler to poll. The final logs report 23 axiom gates,
all within {propext, Quot.sound}; correctionCutoff has no axiom dependency.
The two generic coordinate modules have harmless unused-hypothesis warnings.

| Module | Gates | Final log in /tmp/ |
| --- | ---: | --- |
| `QuaternionHaarOneSidedReciprocalComparison` | 2 | `ym-one-sided-reciprocal-20260930.log` |
| `BF4ExactSlabOneSidedStarComparison` | 1 | `ym-one-sided-star-20260930.log` |
| `SU2QuaternionCrossExteriorPair` | 4 | `ym-cross-exterior-pair-20260930.log` |
| `BF4ExactSlabCrossExteriorReplacement` | 3 | `ym-cross-exterior-replacement-20260930.log` |
| `SU2QuaternionConditionalReplicaMarginal` | 2 | `ym-conditional-replica-marginal-20260930.log` |
| `BF4ExactSlabInPlaceVarianceEnergy` | 3 | `ym-in-place-variance-energy-20260930.log` |
| `BF4ExactSlabCrossExteriorEnergyFubini` | 5 | `ym-cross-exterior-energy-fubini-20260930.log` |
| `GeometricCorrectedLimitOrder` | 2 | `ym-geometric-corrected-limit-order-20260930.log` |
| `BF4ExactSlabReplacementEnergyBound` | 1 | `ym-replacement-energy-bound-20260930.log` |

Sol agents independently implemented coordinate/Fubini and determinant pins;
Luna reviewed the final finite inequality's weights, normalization and factor
two without finding a discrepancy. The parent reviewed and checked each
module. No new sorry, custom axiom or analytic assumption was introduced,
no old sorry was discharged and no frontier statement was weakened.
Root imports were added but no full-root build, audit or guard was run.
Canonical chart states are unchanged. The research cache remains within its
12-hour review interval, so no routine listing scan was repeated.
