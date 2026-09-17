# Actual centered polynomial seeds: construction and boundary

Date: 2026-09-17 UTC. Parent checkpoint: `f3f8ed8`.

The whole-project target remains a nontrivial continuum Yang--Mills theory
on R^4, for every compact simple group, with the required same-theory QFT
axioms and a strictly positive physical Hamiltonian gap. This increment
constructs finite SU(2) polynomial tests. It does not close that target.

## Mathematical choice

The parallel source/mathematical reviews selected a direct Haar telescope
and polynomial inverse construction. An auxiliary Richardson/heat-bath
coercivity theorem is not needed to choose the tests. No auxiliary dynamics
is identified with the physical transfer. The existing intended energy
consumer is `actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`.

Write nu=(V*T^n1)*T^(n+1)1, Z=H[nu], Phi=Z*f-H[nu*f]. Ordinary Haar
telescoping of nu*Phi supplies polynomials tau_i with P_i(tau_i)=0.
For m_i=P_i nu, choose a finite polynomial J_i,k approximating 1/(nu*m_i)
and set seed_i,k=J_i,k*tau_i, q_i,k=weightedResidual_i(nu,seed_i,k).
Every q_i,k satisfies P_i(nu*q_i,k)=0 exactly. This is conditioning on all
other coordinates, not a nested-filtration centering assumption.

## Source map

All paths below are relative to the repository root.

| Constructed result | Declaration and source |
| --- | --- |
| Original partition at 2*n+1 transitions | `mass_compactPartition`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:82` |
| H[nu*Phi]=0 for arbitrary f | `source_mean_zero`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:99` |
| Sum of pieces equals nu*Phi under supported Haar testing | `pieceSum_source`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:164` |
| Exact ordinary conditional zeros and telescope | `project_term_zero`, `lean/YMGap/Continuum/SU2QuaternionHaarBlockTelescope.lean:81`; `telescope_coeff`, same file:125 |
| Constructed positive finite window on nu | `lowerCertificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalWindow.lean:111`; `upperCertificate`, same file:145 |
| Certificate transport without losing unsupported intermediate insertions | `reindex_certificate`, `lean/YMGap/Continuum/SU2QuaternionHaarCertificateReindex.lean:136` |
| Positivity and intervals under selected-coordinate integration | `project_certificate`, `lean/YMGap/Continuum/SU2QuaternionHaarBlockCertificate.lean:136`; `project_interval`, same file:184 |
| Window ell^2 <= nu*(P_i nu) <= u^2 | `denominatorLowerCertificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedWindow.lean:98`; `denominatorUpperCertificate`, same file:119 |
| Finite polynomial inverse with computed tolerance cutoff | `reciprocal`, `lean/YMGap/Continuum/QuaternionHaarPositiveWindowInverse.lean:162`; `approximationCutoff`, same file:210; `approximationInterval`, same file:213 |
| Actual seed, test and exact nu-centering | `seed`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:109`; `test`, same file:116; `test_centered`, same file:125 |
| Division-free polynomial error identity | `weightedResidual_seed_error`, `lean/YMGap/Continuum/SU2QuaternionWeightedResidualApproximation.lean:36` |
| Geometric interval on m_i*(nu*q_i,k-tau_i) | `clearedDefectInterval`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:146` |
| Certificate-level cancellation of positive multipliers | `cancelSquareBound`, `lean/YMGap/Continuum/QuaternionHaarPositiveFloorCancellation.lean:117` |
| Density retained when removing its multiplier | `weighted_norm_floor`, `lean/YMGap/Continuum/QuaternionHaarPositiveFloorCancellation.lean:103` |
| Actual per-piece vanishing square certificate | `pieceDefectSquareBound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedApproximation.lean:150` |
| Computed per-piece tolerance degree and its theorem | `pieceApproximationCutoff`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedApproximation.lean:159`; `piece_defect_haar_square_le`, same file:162 |

The division-free identity is

    m_i*(nu*q_i,k-tau_i) = nu*P_i(e_i,k*tau_i)-m_i*e_i,k*tau_i,
    e_i,k = 1-nu*m_i*J_i,k.

For a certified interval |tau_i|<=B_i, the cleared error has interval
2*u*B_i*rho^k, with rho=1-ell^2/u^2 in [0,1). The displayed absolute-value
notation summarizes witness-bearing polynomial intervals, not a new
pointwise-positivity axiom.

Positive-floor cancellation now gives the concrete, uncleared per-piece
bound, with D_i,k=nu*q_i,k-tau_i:

    H[D_i,k^2] <= rho^(2*k) * 4*u^2*B_i^2/ell^2.

`pieceDefectSquareBound` constructs its square certificate.
`pieceApproximationCutoff` computes a Nat from the original parameters,
input polynomial, coordinate and positive tolerance epsilon.
`piece_defect_haar_square_le` certifies H[D_i,k^2]<=epsilon at every
larger degree. This is a squared-norm tolerance, not a norm tolerance.
The cap B_i is computed from the actual piece polynomial; no centering
or error-budget premise is required of the original input f.

## Exact parameter and equality boundaries

The positive constants ell,u and rate rho retain nome w, cutoff K, spatial
width and boundary depth n. They require 0<w<1 and headCutoff(w)<=K.
The window uses the entire spatial potential and both unequal terminal
depths. No even central density replaces the odd marginal.

The full in-place Haar projection retains raw trailing-zero monomial
aliases. Accordingly `telescope_coeff` stops at input minus full projection.
`partialProjection_constant_padded`,
`lean/YMGap/Continuum/SU2QuaternionHaarBlockTelescope.lean:200`, and
`centered_telescope`, same file:234, establish the constant/zero endpoint
in the appropriate padded or supported-Haar relation. Raw coefficient
equality to a canonical constant is not asserted.

The inverse construction is not a physical time-decay estimate. It may
deteriorate with every regulator. No beta-uniform, width-uniform or
spacing-uniform positive mass is obtained from rho<1.

## Remaining causal joins

1. Assemble the finite family into a single explicit approximation of Phi
   in the same nu norm; retain the supported-Haar telescope endpoint.
2. Choose the additional active-link correction degrees for d_i*G_i*q_i,
   and bound the corrected sum used by `actualResidual_corrected_energy`.
3. Establish a suitable bound on D+2h*R for the chosen family, with the
   actual spatial/depth/cutoff dependence required by the scaling route.
   Positive D cannot be dropped from an upper bound; R remains signed.
4. The stronger uniform original-action estimate, physical spacing/mass
   calibration, continuum passage, full same-theory QFT and every-group
   obligations remain open. No canonical frontier statement was changed.

An explicit finite approximation does not establish a stable decomposition
with uniform cost. The construction does not assume such a budget.

## Verification record

Eleven final focused file checks passed, including all 91 public printed
axiom gates. Every final gate uses only `propext` and `Quot.sound`; the
final logs contain no error, warning, `sorryAx` or classical dependency.
No root/full-tree/full-audit/guard run is claimed. All runs were serialized,
one worker, 20 GiB ceiling, through the monitored launcher with fresh
process/swap preflight. Eleven root imports were added. CI, memory limits,
canonical frontier fields and existing sorrys were unchanged.

The command shape for each source F and corresponding output O was:

    python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
      --check lean/YMGap/Continuum/F.lean \
      --check-output lean/.lake/build/lib/lean/YMGap/Continuum/F.olean \
      --log-file /tmp/LOG

Final local logs (not repository artifacts), with SHA-256:

| Source stem | Log under `/tmp/` | SHA-256 |
| --- | --- | --- |
| SU2QuaternionHaarCertificateReindex | ym-certificate-reindex-20260917.log | `06e132ccd180a6b36792d262fcc0fa8bc1245ac1bf6543febaeffc6b29f79ecc` |
| SU2QuaternionHaarBlockCertificate | ym-block-certificate-20260917.log | `c17ac4d77f7084a94f203cdd5e993512b854c161544681308248aba041c1a847` |
| SU2QuaternionHaarBlockTelescope | ym-haar-telescope-20260917.log | `4165f77c683d532639732af1cb1db6a456b434e18968eeed84252b7486fb742a` |
| SU2QuaternionWeightedResidualApproximation | ym-weighted-residual-error-20260917.log | `7c1959cf2596c730f14eb7030858743c69b15568c3406fdcf10d808d5dfb3d3f` |
| QuaternionHaarPositiveWindowInverse | ym-positive-window-inverse-20260917.log | `cdfc1f2ce6378bddf8a1add1173749d706fd80a491afa9cc316881932c4101c0` |
| QuaternionHaarPositiveFloorCancellation | ym-positive-floor-cancellation-20260917.log | `3fe611ed3386e16b0f9e73715027d4b79fc211e6e168e882237d0e900cb1028c` |
| BF4ExactSlabFixedSpatialActualMarginalWindow | ym-actual-window-20260917.log | `6115260594651c990fa6da140a96aa7054ea23ac3de39ca2a86e56b38f4cfe71` |
| BF4ExactSlabFixedSpatialActualSeedWindow | ym-actual-seed-window-20260917.log | `85cb6b44d98cfbf63d1eca45e43b3210610a50797e43bcb5f884f9e67bd31bbb` |
| BF4ExactSlabFixedSpatialActualSeed | ym-actual-seed-20260917.log | `2cce31423d8430cadcadd9193997a73dab75c098bbae2e52f26bec04557815cb` |
| BF4ExactSlabFixedSpatialCenteredHaarTelescope | ym-centered-haar-telescope-20260917.log | `7095c0a0955f743fea3d262ef4462691f6b42828478d0a18516bc946918a7ee8` |
| BF4ExactSlabFixedSpatialSeedApproximation | ym-seed-approximation-20260917.log | `31a9a0f25fcb784e43ea7401ad10b9e3a06835194ba706dc034cf2203d1381c8` |

Independent source reviews covered the reindex/conditional positivity,
actual product window, partition-centered telescope, weighted error
identity, floor cancellation, per-piece modulus and interpretation. They
found no mathematical blocker; two audit line citations were corrected.

During checking, `restored_prefix` in the selected projection proof initially
inherited `Classical.choice` from an automated proof of a conjunction.
Replacing it by an explicit pair of arithmetic proofs removed that dependency.
The final selected-coordinate gates report only `propext` and `Quot.sound`.
This did not require changing any imported theorem or weakening a statement.
