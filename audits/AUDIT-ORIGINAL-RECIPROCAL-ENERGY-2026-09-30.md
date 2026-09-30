# Original reciprocal variance and conditional residual energy

## Goal and scope

The unchanged goal remains OPEN: constructive continuum Yang--Mills on
R^4 for every compact simple group, with SAME-theory QFT axioms,
nontriviality and a finite positive physical Hamiltonian mass gap.

This checkpoint concerns the original finite-cutoff SU(2) slab action,
at rational nome 0<w<1 and K>=headCutoff(w), and a physical link belonging
to that slab. The operator is the existing conditional projection on
ordinary weighted L2, NOT OS time or the physical Hamiltonian.

Let A be the original incident heat product, B the entire complementary
action, D the integrated head normalizer, N(p) the actual inserted
normalizer, and G_k the finite positive reciprocal of D. The original
full-action form is F. The literal conditional approximant A_k p is
project_j(p*A)*G_k(project_j A), pinned to the existing conditional update
by the preceding checkpoint.

## Exact finite identities

The new finite loss retains the same input and action:

    loss_k = F(p,p) - F(p,A_k p)
           = H_exterior[(N(p^2) - N(p)^2 G_k) B].

The signed polynomial identity is

    N(p^2) - N(p)^2 G_k
      = (D N(p^2) - N(p)^2) G_k + (1-D G_k) N(p^2).

Thus loss_k = varianceEnergy_k + normalizationError_k. In particular,
the unnormalized determinant D N(p^2)-N(p)^2 is NOT silently identified
with conditional residual energy: its finite reciprocal and the
normalization defect both remain in the equation.

Paths in this table start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Checked finite content |
| --- | --- | --- |
| `approximation_pairing_pin` | `BF4ExactSlabReciprocalEnergyPairing.lean:81` | Actual original pairing becomes N(p)^2 G_k against B |
| `finiteLoss_pairing_pin` | `BF4ExactSlabReciprocalEnergyPairing.lean:108` | Exact loss integral above |
| `lossPolynomial_split`, `finiteLoss_split` | `BF4ExactSlabReciprocalEnergyPairing.lean:118`, `:145` | Signed cancellation before estimating either term |
| `replicaIntegral_pin` | `BF4ExactSlabReciprocalEnergyPairing.lean:165` | Actual two-head replica square with lifted G_k B equals twice varianceEnergy_k |
| `reciprocalDefect_haar_bounds` | `QuaternionHaarReciprocalDefectBound.lean:78` | 0<=H[(1-DG_k)V]<=rho^k H[V] for every certified nonnegative V |
| `normalizationError_bounds` | `BF4ExactSlabReciprocalEnergyError.lean:45` | 0<=normalizationError_k<=rho^k F(p,p) for the original action |
| `errorCutoff`, `normalizationError_le` | `BF4ExactSlabReciprocalEnergyError.lean:58`, `:61` | Explicit absolute-error cutoff |
| `varianceEnergy_nonnegative` | `BF4ExactSlabReciprocalEnergyError.lean:71` | Nonnegative reciprocal-weighted variance from actual certificates |

The defect bound uses the existing `tailSquare_certificate` and
`original_norm_pin` at
`lean/YMGap/Continuum/BF4ExactSlabStarExteriorSeedNorm.lean:96` and `:105`.
No extra positivity hypothesis or coefficient-norm replacement is needed.
Here rho=1-ell/U, ell=headFloor(w)^d, U=prefixCap(w)^d and d is the actual
incident-face count. Nome dependence remains explicit. The cutoff is
geometricCutoff(rho,F(p,p),epsilon); there is no spacing-uniform assertion.

## Constructed limits on the SAME original completion

`BF4ExactSlabReciprocalEnergyLimit.finiteLossCauchy` at
`lean/YMGap/Continuum/BF4ExactSlabReciprocalEnergyLimit.lean:54` obtains
explicit rational-stream Cauchy data from the existing conditional
approximants. `finiteLoss_limit_eq_residual_norm` at the same path, line97,
identifies its quotient limit with
`normSq (projections.residual link (embedV F p))`. This is the existing
full-action projection, not a newly supplied inverse or kernel law.

`BF4ExactSlabReciprocalVarianceLimit.varianceCauchy` at
`lean/YMGap/Continuum/BF4ExactSlabReciprocalVarianceLimit.lean:52` uses

    M_variance(epsilon) = max(M_loss(epsilon/2), errorCutoff(epsilon/2)).

`variance_limit_eq_residual_norm` at the same path, line107, identifies
its CReal quotient with that SAME residual energy. `replicaCauchy` at
line120 uses M_replica(epsilon)=M_variance(epsilon/2), and
`replica_limit_eq_twice_residual_norm` at line156 identifies the limit of
the literal replica integrals with the sum of two copies of that energy.
Every modulus is retained as data; limit uniqueness extracts no modulus
from an erased existential. The proof factors scalar limit arguments into
generic lemmas to avoid normalizing the entire concrete polynomial action.

## Original path-cut transport and remaining join

The following additional steps are proved (paths again start at
`lean/YMGap/Continuum/`):

| Declaration | File:line | Content |
| --- | --- | --- |
| `prefix_increment_transport` | `SU2QuaternionReplicaPathIncrement.lean:50` | Exchanging the prefix converts its next increment into replacement of one block |
| `weighted_prefix_increment_change` | `SU2QuaternionReplicaPathIncrement.lean:97` | Exact weighted Haar change of variables on the doubled carrier |
| `weighted_cut_comparison_reverse` | `BF4ExactSlabReplicaCutReverse.lean:48` | Swapped weight bounded by original weight, with the same actual crossing-face count |
| `prefixLinks`, `cutSwap_prefix` | `BF4ExactSlabReplicaPrefixCut.lean:47`, `:74` | Literal raw physical-prefix recoding and equality of the actual swaps |
| `original_prefix_increment_bound` | `BF4ExactSlabReplicaPrefixCut.lean:89` | Path-increment square bounded by a one-block replacement square under the original pair action |

Writing l=headFloor(w), u=prefixCap(w), b=crossingCount(prefixLinks j),
W for the original full weight and delta_j for replacement by the other
replica's block, the last theorem is

    (l^2)^b H_2N[W(x)W(y) * prefixIncrement_j(f)^2]
       <= (u^2)^b H_2N[W(x)W(y) * delta_j(f)^2].

The orientation matters: the previous forward cut bound did not directly
provide this upper bound. Its reverse is proved by the actual involution,
including transport of the joint square insertion.

The replica integral here duplicates ONLY the selected head link, with
one shared exterior, and retains G_k B lifted by two head blocks. The
existing cross-exterior comparison instead exchanges the exterior between
two full replicas while keeping the updated coordinate shared. These are
different coordinate arrangements. An exact path/insertion identity is
still needed to join them; names or diagrams do not provide that equality.
In particular, the one-block replacement in the new path bound comes from
an independent FULL replica, not a conditional refresh at the original
exterior. The next conditional-kernel/Fubini comparison must preserve BOTH
normalizers and the original pair partition before the path sum can be
joined to residual energy. The raw prefix has not been proved time-layer
ordered; the existing eight-color schedule is not such an ordering.

The candidate N*(prefixCap/headFloor)^(2C+12) remains an unproved finite
Poincare budget. Its area-dependent loss would not by itself supply useful
signed spatial/scaling control. No conditional-generator coercivity,
OS-transfer gap, continuum construction, physical mass or every-group
closure is asserted. Canonical chart states are unchanged.

## Verification boundary

All eight new modules passed focused serialized checks through
`scripts/safe_lean_build.py`, with one worker, a 20 GiB worker ceiling,
12 GiB OS reserve and continuous safety telemetry. Manual checks of live
long-running jobs were spaced about five minutes apart. The final logs
contain 48 printed axiom gates, all within {propext, Quot.sound}.

| Module | Gates | Final log in /tmp/ |
| --- | ---: | --- |
| `BF4ExactSlabReciprocalEnergyPairing` | 10 | `ym-reciprocal-energy-pairing-20260930.log` |
| `QuaternionHaarReciprocalDefectBound` | 6 | `ym-reciprocal-defect-bound-20260930.log` |
| `BF4ExactSlabReciprocalEnergyError` | 6 | `ym-reciprocal-energy-error-20260930.log` |
| `BF4ExactSlabReciprocalEnergyLimit` | 6 | `ym-reciprocal-energy-limit-20260930.log` |
| `BF4ExactSlabReciprocalVarianceLimit` | 9 | `ym-reciprocal-variance-limit-20260930.log` |
| `SU2QuaternionReplicaPathIncrement` | 6 | `ym-replica-path-increment-20260930.log` |
| `BF4ExactSlabReplicaCutReverse` | 1 | `ym-replica-cut-reverse-20260930.log` |
| `BF4ExactSlabReplicaPrefixCut` | 4 | `ym-replica-prefix-cut-20260930.log` |

The last three checks completed in their initial call. Earlier limit
attempts hit deterministic elaboration timeouts, not a proved mathematical
obstruction; the generic scalar proofs resolve those timeouts at the
default heartbeat budget. A path lemma has a harmless unused-hypothesis
warning. No new sorry, custom axiom or analytic assumption was introduced,
no old sorry was discharged and no frontier statement was weakened.
Root imports were added but no full-root build, audit or guard was run.
