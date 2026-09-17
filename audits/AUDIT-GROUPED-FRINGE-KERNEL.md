# Group the actual fringe before charging its energy cost

Date: 2026-09-17 UTC. Parent checkpoint: `e965847`.

The whole-project goal remains constructive continuum Yang--Mills on R^4
for every compact simple group, with the required same-theory QFT axioms,
isolated vacuum and positive finite physical Hamiltonian mass gap. This
increment proves an exact finite original-action sector estimate only.

## Mathematical contraction

Set g_n=T^n1, a=V*g_n, t=T^(n+1)1 and nu=a*t. The existing concrete
residual at inactive coordinate i is q_i=weightedResidual_i(nu,seed_i).
`fringeResidual_centered`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeDual.lean:94`, proves
P_i(a*q_i)=0: t is independent of that coordinate. The original kinetic
product has no factor at i, so it annihilates a*q_i under Haar testing.

The same is true of their signed sum r. Sum the exact jump-pairing identity
FIRST, then apply Cauchy--Schwarz once:

    H[p*T(g_n*r)] = 0                 for every Haar test p,
    H_edge[jump(f)*jump(r)] = 2*H[nu*f*r],
    E_gn(r) = H[nu*r^2],
    H[nu*f*r]^2 <= E_gn(f)*H[nu*r^2].

This is an actual norm of the entire signed test. No sum of component norms,
link-count factor, inverse-density comparison or spatial heat-floor loss
is introduced. The positivity guards 0<w<1 and headCutoff(w)<=K enter
only the last Cauchy--Schwarz inequality, not the algebraic identities.

## Checked source map

| Result | Declaration and source |
| --- | --- |
| Entire absent-coordinate family annihilates all Haar pairings | `absent_sum_pair_zero`, `lean/YMGap/Continuum/SU2QuaternionAbsentHeatFamily.lean:61` |
| Exact whole-family jump identity | `absent_sum_jump_pairing`, `lean/YMGap/Continuum/SU2QuaternionAbsentHeatFamily.lean:139` |
| Concrete sum of actual marginal residuals | `fringeSum`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:90` |
| Actual transfer annihilation, retaining g_n | `fringeSum_transfer_pair_zero`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:100` |
| Same original edge and marginal | `fringeSum_jump_pairing`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:117` |
| Whole fringe energy equals its actual marginal norm | `fringeSum_energy_eq`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:140` |
| One coefficient-one dual estimate | `fringeSum_dual_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:152` |
| Existing approximation seeds supplied without new centering hypotheses | `actualFamily_fringe_dual_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:187` |
| Exact active-plus-grouped-fringe corrected-sum partition | `correctedSum_partition`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:198` |

The two generic sum identities use only finite linearity and existing
`productMap_absent_pair_zero`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:369`, and
`erased_jump_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:242`.
They retain empty families, repetitions and signed summands. There is no
assertion of raw output coefficient-zero.

## Effect on the proof path

The previous corrected-family approximation remains proved and unchanged:
`approximationCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:118`.
Its energy consumer `approximant_energy`, same file:129, still displays
the old exact D+2h*R cost. This increment does NOT replace that theorem or
claim a uniform bound on that cost. Instead it provides a sharper way to
pay the entire inactive portion, with an exact pin to the existing sum.

Next: combine the active dual flow and grouped fringe jump while retaining
their cross pairings, then bound the resulting cost relative to the original
centered observable. The grouped fringe need not be orthogonal to the
active remainder. A test's construction label does not determine whether
it belongs to an inactive transfer kernel; additional kernel membership
may permit further grouping, but is not supplied by the current theorem.

The read-only mathematical review also identified a candidate diagnostic:
unused-coordinate observables may give large componentwise inverse-density
costs even when their combined test lies in one transfer kernel. The proposed
literal-order/private-face amplification calculation has NOT been formalized
or independently kernel-checked. It is not recorded as an actual-action
counterexample, a refutation of combined D+2h*R control, or a no-go theorem.
The checked grouping theorem does not depend on that diagnostic.

Precise scope: the kernel statement concerns T(g_n*r) on the finite
original Haar carrier. It does not assert T(r)=0, raw polynomial equality,
a completed OS-kernel theorem, or physical-time decay. Uniform full-sector
control, physical calibration, continuum passage, full same-theory QFT
and every compact simple group remain open.

## Verification

Both new modules passed focused serialized checks through the monitored
launcher, with one worker, unchanged 20 GiB ceiling and fresh process/swap
preflight. All ten printed gates use only {propext, Quot.sound}. Final logs
contain no errors, warnings, sorryAx or classical dependencies. Two imports
were added to the root; root/full-tree/full-audit/guard NOT run. No existing
sorry, canonical frontier, CI configuration or safety limit was changed.

An independent read-only mathematical review passed the annihilation scope,
endpoint weights, factors two/four, same-nu norm and actual seed instance.
The final corrected-sum partition was additionally kernel-checked.

Final local log SHA-256 values (logs are not repository artifacts):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| ym-absent-heat-family-20260917.log | 2 | `8d304181514b636d0db8e893190ce8b7e1f507939d803120643598c0b578022b` |
| ym-fringe-kernel-20260917.log | 8 | `46cb31f9ee55daa0654962a75536e2ec0db458833733307b604402f8ba637d5a` |
