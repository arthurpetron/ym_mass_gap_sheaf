# Centered fringe extraction in the original temporal energy

Date: 2026-09-17 UTC. Parent checkpoint: `78a1684`.

Whole-project goal: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT structure, isolated
vacuum and a strictly positive finite physical Hamiltonian mass gap.
This checkpoint proves finite original-action identities and error bounds;
the whole-project target remains OPEN.

## Exact result

Retain the original transfer T=K V, g_n=T^n1 and nu=V*g_n*T(g_n).
For the previously constructed spatial fringe projection P_F, put

    m=P_F(V), M=P_F(V*f), R=m*f-M,
    r=J_k*R, b=J_k*M,
    Z=H[nu]>0, b0=b-H[nu*b]/Z.

Here J_k is the existing certified finite polynomial approximation to 1/m.
Only the explicit positive rational Z is divided by in the scalar centering.
The original observable f and fringe part r are not rescaled.

For supported f, the new results give

    H[nu*r]=H[nu*b0]=0, <r,b0>_nu=0,
    ||r||_nu^2+||b0||_nu^2 <= ||f||_nu^2,
    E_gn(r+b0) = ||r||_nu^2+E_gn(b0).

If H[nu*f]=0, then for any epsilon>0 and every degree at least the
existing relativeApproximationCutoff(epsilon), e=f-r-b0 satisfies

    ||e||_nu^2 <= epsilon*||f||_nu^2,
    E_gn(e) <= 2*epsilon*||f||_nu^2.

The mean-zero condition on f is essential to this centered error argument.
It is not needed for the joint norm budget or exact energy split.

## Declaration map and proof mechanism

| Result | Declaration and source |
| --- | --- |
| Transfer-null component has exactly its original marginal energy | `terminal_kernel_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKernelEnergySplit.lean:146` |
| Orthogonal transfer-null part splits off with coefficient one | `terminal_kernel_energy_split`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKernelEnergySplit.lean:159` |
| Actual extracted polynomials | `fringePart`, `activePart`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionEnergy.lean:53`, `:57` |
| Original mean and tested transfer vanish for r | `fringePart_mean_zero`, `fringePart_transfer_zero`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionEnergy.lean:76`, `:83` |
| Uncentered pieces already have an exact energy split | `extracted_energy_split`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionEnergy.lean:97` |
| Explicit scalar centering and exact mean removal | `center`, `center_mean_zero`, `lean/YMGap/Continuum/QuaternionHaarNormalizedCenter.lean:106`, `:127` |
| Subtracted mean-square correction, hence coefficient-one reduction | `center_norm_identity`, `center_norm_le`, `lean/YMGap/Continuum/QuaternionHaarNormalizedCenter.lean:139`, `:164` |
| Constructed centered active part, still fringe-independent | `centeredActivePart`, `centeredActivePart_independent`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:56`, `:65` |
| Orthogonality and joint norm budget | `centered_pieces_orthogonal`, `centered_pieces_norm_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:76`, `:91` |
| Centering the error changes only b | `centered_error_pin`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:102` |
| Same relative-error degree remains sufficient | `centered_error_norm_le_tolerance`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:121` |
| Exact split for the genuinely centered active polynomial | `centered_extracted_energy_split`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:139` |
| Same original approximation-error energy is small | `centered_error_energy_le_tolerance`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:152` |
| E(f)<=2||f||^2 and E(f+q)<=2E(f)+2E(q) | `energy_le_two_norm`, `energy_add_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEnergyNormBound.lean:83`, `:134` |

The kernel premise is H[p*T(g_n*r)]=0 for every Haar test p. It is not
coefficientwise T(r)=0. The direct mixed term vanishes by that premise;
the reverse mixed term uses the existing original V-weighted symmetry,
`transferStep_weighted_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`.
No mixed term is discarded or assumed positive.

The energy upper and triangle bounds use the same positive full edge
measure and its exact diagonal marginal identity. They do not assume
positive semidefiniteness of the one-step transfer and are not estimates
for a link-update/heat-bath generator.

## Parameters, status and limits

The positivity guards remain 0<w<1 and headCutoff(w)<=K. The generic
energy split itself needs no positivity. The scalar centering identity
and its second-moment reduction require only positive rational H[W],
not a pointwise positivity premise on a generic W.

J_k and the relative-error modulus retain nome/cutoff/width dependence
but have no terminal-depth or observable parameter. The marginal nu and
the centering scalar H[nu*b]/H[nu] DO depend on depth. No uniform absolute
error, coupling-uniform physical gap, spatially uniform floor, or
completed projection has been inferred from the relative estimate.

These algebraic projection and energy arguments provide no new
non-abelian coercivity mechanism. The substantive missing inequality is
still a regulator-controlled LOWER bound on E_gn(b0) in its same norm.
Fringe independence does not imply the original per-link conditional
centering required by the older FamilyCost consumer.

The eventual full-gap transfer is not proved in this checkpoint. In
particular, the factor-two triangle inequality alone does not preserve
a proposed sharp active coefficient; a sharp passage needs finer mixed
energy control. The positive-small-nome completed branch is preserved,
not generalized. Spatial/scaling control, physical calibration, full
same-theory OS/QFT and every-group realization remain OPEN.

## Next action-specific test, not a new assumed interface

A parallel source review proposes proving unique incidence for each
spatial face touching the fringe. Define a fully-active face by requiring
every link in its `edgesOf` list to have its `baseLinks` index in
`activeBlocks`. The proposed witness for a non-fully-active spatial face
is its far link B, if that link is fringe, and otherwise C. The desired
constructive witness includes membership in that face, fringe membership,
and absence from every other spatial face.

This is an UNPROVED geometry claim, not a new Lean declaration. The source
definitions are `spatialFaces_mem_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFacePlacement.lean:98`;
`activeBlocks`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:83`;
and `faceLinkA/B/C/D`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquettePathGram.lean:43` through `:46`.
The review's coordinate check suggests that the far B/C links on the
positive boundary have unique incidence because all face bases are
strictly interior. It is not evidence of a kernel-checked cancellation.

If that witness is proved, the next proposed mathematical statement is
H[V*q]=H[V_A*q] for supported fringe-independent q, where V_A is the
UNCHANGED heat-prefix product over fully-active spatial faces. Existing
all-spin cancellation is available in `original_character_link_zero`,
`lean/YMGap/Continuum/BF4ExactSlabSingleLinkCharacterSelection.lean:53`;
the direct fixed-slice coordinate form is `any_slot_zero`,
`lean/YMGap/Continuum/SU2QuaternionOrientedWordSelection.lean:128`.
The actual fixed-slice coordinate pin and spectator independence must be
proved, not inherited from the different corrected-slab carrier.

The intended next consumer is a tested ORIGINAL transfer equality on
fringe-independent inputs, using `productMap_pairing`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:247`.
Both the boundary cancellation and that transfer equality remain OPEN.
Do not demand raw coefficient equality where Haar-tested equality
suffices. Conversely, do not assert that fringe integration preserves
a local action until this particular geometry and cancellation are proved.
Even successful cancellation would leave the active coercivity estimate
open; it would identify its actual interaction, not bound it.

## Verification

Five new modules passed final focused, serialized one-worker checks via
the monitored launcher, unchanged 20 GiB ceiling and fresh process/swap
preflight. All 33 printed gates use only {propext, Quot.sound}. Final logs
contain no errors, warnings, sorryAx or classical dependencies.
Intermediate checks required a lambda-layout fix, an explicit Haar-block
argument and explicit inclusion of proof-only positivity parameters;
all were rechecked successfully. No actual sorry was introduced/discharged.

Independent read-only mathematical review passed the centered error sign,
unchanged original marginal and fringe, energy split, parameter scope,
and remaining active-sector obstruction. The final concrete error-energy
consumer was additionally kernel-checked. Five root imports were added;
root/full-tree/full-audit/guard NOT run. No canonical frontier statement,
CI setting, safety limit or external literature scan changed.

Final local log SHA-256 values (logs are not repository artifacts):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| ym-kernel-energy-split-20260917.log | 2 | `4532e2f0fe7681081d4f39fce705c2cc427db979bfd7f313947ef27aa4b51c29` |
| ym-fringe-projection-energy-20260917.log | 9 | `dbacdea504393b0498bfe46d32182f9806a9f4ed9dae519a1c01cc972e504668` |
| ym-normalized-center-20260917.log | 10 | `8b0570943a9f960db56b4bd3fc4f3caee0ddd0af6c6a1f590ab843e149c12662` |
| ym-energy-norm-bound-20260917.log | 2 | `58ecc6176f1d6939bf7c852b6af3baa301d6ff6e5a7c3e9cbcf31f9ac7e34017` |
| ym-centered-fringe-extraction-20260917.log | 10 | `7de6846db4ac27740c71dee90009905e923e7604be17bfb45e0c4a5b3976230b` |
