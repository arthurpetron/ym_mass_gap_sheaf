# Original-action projection sweep: exact loss, not spatial closure

## Checked increment

Write C_i for the existing completed conditional projection and R_i=I-C_i.
For the forward schedule i_1,...,i_m, set x_0=x and x_j=C_{i_j}x_{j-1}.
The new theorem checks, in the original constructive-real quotient,

    sum_j ||R_{i_j} x_{j-1}||^2 = ||x||^2 - ||x_m||^2.

The summands use the actual intermediate states. No free-product norm,
deleted action, spectral assumption or strict-contraction hypothesis occurs.
The corresponding signed pairing differences telescope as well.

| Declaration | Source | Content |
|---|---|---|
| `Family.loss_eq` | `lean/YMGap/Continuum/GNSProjectionSweep.lean:133` | Exact norm loss for a finite forward schedule. |
| `Family.pairingLoss_eq` | `lean/YMGap/Continuum/GNSProjectionSweep.lean:156` | Signed pairing telescope against one unchanged completed test. |
| `Family.sweep_preserves_sector` | `lean/YMGap/Continuum/GNSProjectionSweep.lean:185` | Preserves the orthogonal complement of the common fixed vectors. |
| `Family.residual_after_own` | `lean/YMGap/Continuum/GNSProjectionSweep.lean:192` | The selected residual vanishes immediately after its own update. |
| `Family.residual_update` | `lean/YMGap/Continuum/GNSProjectionSweep.lean:216` | Exact correction R_i C_j x = R_i x - R_i R_j x. |
| `projections` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:56` | Constructs the family from original physical conditional operators. |
| `sweep_loss` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:65` | Actual original-action instance of the loss identity. |
| `signed_pairing_telescope` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:69` | Actual original weighted signed-pairing identity. |
| `nonneighbor_residual_norm` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:84` | Nonneighbors cannot increase a selected residual. |
| `correction_norm` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:100` | A neighboring correction is bounded by the actual one-step norm loss. |
| `neighbor_count` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:107` | At most 25 neighboring entries in a duplicate-free schedule. |
| `local_test_pairing` | `lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:115` | Pairing unchanged if every updated link is omitted by the literal test support. |

All operators use one `fullData` at fixed w, K and extent, for 0<w<1 and
K>=headCutoff(w). `fullData` in
`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49` retains the entire
original face product. It uses the UNNORMALIZED weighted pairing of
`weightedGNSData` in
`lean/YMGap/Continuum/QuaternionHaarWeightedCauchySchwarz.lean:63`.
The new family fields are discharged by the existing actual self-adjointness
and idempotence theorems; they are not new open analytic assumptions.

The generic identities are group-agnostic Hilbert-space algebra. The physical
instance is the present SU(2) construction. The number 25 is four-dimensional
incidence geometry, independent of coupling and volume; it is NOT a gap or a
coercivity constant. No beta-uniform positive mass is asserted.

## What the increment does not prove

The old free-centered sector is not reintroduced. The preserved sector is
defined by orthogonality to ALL common fixed vectors of the selected
projections. There is no theorem here identifying that fixed space with the
constants, or its complement with an OS vacuum complement.

The count 25 and one-step inequalities are not yet the completed finite-sum
estimate for total final residual energy. Nor do they provide a positive
original-action coercive lower bound on that energy. In particular there is
no proved strict sweep rate in these files.

Even a strict sweep rate would concern conditional-update time, not physical
time or spatial distance. A sequential sweep may chain neighbors through the
slab in one pass; the one-step `conditionalProjection_localRepresentative`
in `lean/YMGap/Continuum/BF4ExactSlabStarConditionalLocality.lean:141` does not
give a volume-independent propagation radius for an arbitrary sweep.

The existing `exactPreimage` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointNeumannInverse.lean:83`
concerns the separate fixed-spatial time-transfer construction, not the
conditional sweep. No sweep-to-spatial-covariance theorem was found in that
module, its `NeumannBound` companion, or the inspected `StarConditional*`,
`StarIndependentProbe` and rooted-response modules. The normalization
identity `finite_covariance_cleared` in
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:176` is available,
but supplies no off-diagonal estimate.

## Consumer review and next bounded work

The intended analytic consumer remains the original normalized signed
response, `covariance_response_bound_of_rooted` in
`lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:118`.
The present sweep identities do not discharge its bound.

Before adding a sweep resolvent, address the missing spatial argument:

1. Construct a bounded-depth physical schedule and prove layer locality.
   Source review found the candidate color `(direction, height(base) % 2)`.
   `height_addE` in `lean/YMGap/Continuum/Z4EvenLinkMinimum.lean:24` and
   `edgesOf` in `lean/YMGap/Continuum/ClusterCount4DProgress.lean:147` support
   eight colors: parallel edges of a plaquette have opposite base parity.
   The coloring, partition and layer-locality proof are NOT implemented here.
2. Prove the bounded-degree total-energy estimate on this SAME completion;
   then establish, rather than assume solved, its useful original-action
   lower bound. Its coupling/volume/scaling dependence must remain explicit.
3. Prove the spatial signed-covariance join with the original normalization.
   An ordinary conditional-dynamics estimate is not an OS or Hamiltonian gap.

These are working proof tasks, not a new canonical frontier bundle.
Physical spacing, nontrivial continuum survival, mass calibration, full QFT
axioms and the every-compact-simple-group target remain open.

## Targeted primary-source check

[Anshu--Arad--Vidick, section III, Lemma 2 and Corollary 3](https://arxiv.org/html/1602.01210)
derive a squared-degree loss estimate for finite families of projectors with
bounded noncommutation degree. Turning it into strict contraction requires a
positive energy lower bound. Their layered discussion separately supplies the
locality mechanism. This is a proof template, not an imported Lean theorem or
a verified application to the present Yang--Mills completion.

[Aharonov--Arad--Landau--Vazirani, sections 4 and 6](https://arxiv.org/pdf/1011.3445)
use layered causal cones together with a gap assumption to obtain correlation
decay. They do not furnish our missing original-action lower bound. This was
a targeted source check, not another math-ph listing refresh.

## Verification

Both new modules passed focused monitored checks, one worker and mandatory
20 GiB ceiling. All 12 generic and 10 physical printed gates report exactly
{propext, Quot.sound}; no final warnings or errors. Initial elaboration errors
were recursive-parameter and local-notation field syntax, corrected without
changing the mathematical claims. Sol independently reviewed the final source
for action/carrier pins and proof scope; a separate source review located the
spatial obstruction and eight-color candidate.

No competing build, full-tree build/audit, new sorry, classical axiom,
canonical-field edit, or chart-marker change. After launching the final
check, source review and targeted literature work proceeded before collecting
its result, without repeated status polling.
