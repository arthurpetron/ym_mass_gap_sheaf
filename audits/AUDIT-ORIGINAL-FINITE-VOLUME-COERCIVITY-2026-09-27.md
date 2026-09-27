# Constructed original-action finite-volume coercivity

## Mathematical increment

For 0<w<1, finite extent, and every K>=headCutoff(w), put

    F = number of original physical faces
    m = headFloor(w)^F > 0
    M = prefixCap(w)^F > 0
    delta = m/M > 0.

The original full-action form, its constant vector U, and its actual
completed link conditionals P_i are retained. For every supported polynomial
p with original mean zero, B(p,U)=0, the new theorem proves

    delta B(p,p) <= sum_i ||(I-P_i) embed(p)||^2.

This is an actual constructed lower estimate, not a certificate field
assuming coercivity. It is uniform in the late heat cutoff K. The all-face
exponent remains explicit: no volume-, nome-, or physical-spacing-uniform
lower bound is claimed.

## Causal proof and source map

1. `square_telescope` and `haar_efron_stein`,
   `lean/YMGap/Continuum/SU2QuaternionHaarEfronStein.lean:93` and `:252`,
   give the sharp ordinary product-Haar variance inequality. Commuting
   coordinate projections contract each exact telescope term; the constant
   is one, not the number of links. Zero blocks are included.
2. `centered_norm_le_haar_variance` and `centered_norm_le_free_energy`,
   `lean/YMGap/Continuum/BF4ExactSlabHaarVarianceComparison.lean:77` and
   `:102`, use ORIGINAL mean zero to subtract the free-Haar mean times U
   without decreasing the original norm. The full-action ceiling gives
   B(p,p)<=M*sum_i Haar((p-E_i p)^2). No assumption that free and interacting
   means agree is used.
3. `conditional_residual_inplace_floor`,
   `lean/YMGap/Continuum/BF4ExactSlabStarHaarResidualFloor.lean:280`,
   proves m*Haar((p-E_i p)^2)<=||(I-P_i)embed(p)||^2. Free-Haar orthogonality
   makes E_i p the least-square exterior approximation. The full-action
   floor applies to every finite inverse probe; passage through the actual
   inverse Cauchy representative retains the same completed residual.
4. The coordinate pin uses the existing `restored_prefix`, now public at
   `lean/YMGap/Continuum/SU2QuaternionHaarBlockCertificate.lean:72`.
   `physical_schedule_index_perm`,
   `lean/YMGap/Continuum/BF4ExactSlabPhysicalScheduleIndex.lean:58`,
   proves that the colored physical schedule covers precisely the original
   Haar coordinate indices, once each. The schedule order is not asserted
   to preserve the sweep operator under arbitrary permutations.
5. `free_energy_le_original_dirichlet`, `dense_centered_coercivity_mul`,
   and `dense_centered_coercivity`,
   `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeCoercivity.lean:119`,
   `:136`, and `:163`, compose the actual inequalities, first division-free
   and then with the constructed positive reciprocal of M.
   `coercivity` (`:88`) has no K argument; `coercivity_positive` (`:93`)
   proves strict positivity without an analytic hypothesis.

The form is the unnormalized original integral. A partition factor is not
missing: every original norm uses that form and its mean-zero condition is
unchanged by positive scalar normalization. No per-step preservation of
the free-centered sector is assumed. The energy in this theorem is the sum
of residual norms at ONE input state, not sequential sweep loss.

## Completed carrier and actual covariance consumer

`completed_centered_coercivity`,
`lean/YMGap/Continuum/BF4ExactSlabCompletedFiniteVolumeCoercivity.lean:197`,
extends the same coefficient to all completed states orthogonal to the
original constant, at K=headCutoff(w)+stage for every stage. The physical
`centeredCauchy_same_class` constructs centered representatives in the SAME
quotient. Input and actual conditional-output pairings converge; the exact
`single_loss` identity supplies residual-norm convergence. Closed eventual
order passes the finite sum inequality to the limit. No representative
choice, extra analytic input or loss in delta occurs.

`finite_volume_reverse_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:149`, applies
that coercivity to the actual B u=S* S u. The existing geometric 625 bound
is applied to the REVERSE sweep at S u. Only the list of final residual
tests is permuted; no operator order is changed. Thus

    delta ||B u||^2 <= 625 (||S u||^2 - ||B u||^2)
    c ||B u||^2 <= 2 ||S u||^2,  c=2+2*delta/625>2.

The coefficient and its strict inequality are `reverseCoefficient` (`:92`)
and `reverseCoefficient_gt_two` (`:121`). `coupled_auxiliary_reverse_energy`
(`:181`) supplies this estimate at every actual coupled auxiliary, using
the proved preservation of ORIGINAL completed centering, not free-link
centering.

`T_lower_and_step` and `T_positive`,
`lean/YMGap/Continuum/ChebyshevAboveOne.lean:25` and `:53`, derive the
positive denominator guard from the scalar recurrence at x>=1.
`finiteCovariance_sq_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeChebyshevCovariance.lean:64`,
therefore proves

    Cov(p,q)^2 <= T_n(c-1)^(-2) Var(p) Var(q)

under the original 16*n cone separation. BOTH variances, covariance and
partition reciprocal are the originals. Neither reverse energy nor
denominator positivity is an assumed argument anymore. In a fixed box the
cone-separation premise need not hold for arbitrarily large n; this is not
an infinite-distance conclusion at fixed volume.

## Targeted literature comparison

Rai et al., [A Hierarchy of Spectral Gap Certificates for Frustration-Free
Spin Systems, v3](https://arxiv.org/html/2411.03680v3), section 2 and
Appendix D, was reviewed specifically; no routine math-ph scan was run.
Its finite-dimensional, translation-invariant spin setting is not the
original continuous SU(2) slab carrier. Appendix D distinguishes an
extensive error from unrestricted local negative slack from a correction
that annihilates the local ground sector. This is a useful certificate
design constraint, not a verified import of its gap criterion. No matrix,
ground projector, or positivity result from that paper is assumed here.
The present lower estimate is independently constructed from the existing
original heat-weight floor and ceiling.

## Verification boundary and remaining target

The six modules through dense coercivity passed focused serialized checks
with `scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`:
HaarBlockCertificate (4 printed gates), HaarEfronStein (6),
HaarVarianceComparison (4), StarHaarResidualFloor (11),
PhysicalScheduleIndex (4), and FiniteVolumeCoercivity (6).
All 35 printed gates are within {propext, Quot.sound}. Draft elaboration
failures were repaired before the final passing checks. A parallel source
review independently checked the centering/normalization and warned against
identifying same-state Dirichlet energy with sequential loss.

Four further focused checks passed: CompletedFiniteVolumeCoercivity (1
printed gate), FiniteVolumeReverseEnergy (6), ChebyshevAboveOne (2), and
FiniteVolumeChebyshevCovariance (3). The total is ten modules and 47 gates,
all within {propext, Quot.sound}. Independent Sol review checked the full
completed-to-reverse-to-original-covariance join and the separation boundary.
The root import list is updated but was not built or audited.

No new sorry, axiom, classical input, canonical field or chart marker is
introduced. These are narrow checks, not a root/full-tree audit. One
compiler at a time and continuous pressure telemetry were used; every
check completed during its initial call, so no live job was repeatedly
polled. The goal remains OPEN.

The essential remaining improvement is a useful same-action estimate on
a justified scaling family, without the present all-volume floor/cap cost.
The comparison argument does not establish a non-abelian physical mechanism:
its quantitative coefficient and finite-volume scope must not be discarded
to infer a group-independent continuum gap.
Conditional-link dynamics is not OS time. Same-theory continuum/OS/QFT,
nontrivial survival, physical Hamiltonian mass calibration, every compact
simple group and the Clay theorem remain open. No unchanged ASCII chart
is reprinted.
