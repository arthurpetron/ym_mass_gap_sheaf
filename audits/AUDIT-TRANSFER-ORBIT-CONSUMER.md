# Transfer-orbit consumer audit

Date: 2026-09-17 21:33 UTC. Source baseline:
`be1afb3896d0b0d3ea2ebb5a939677ac301b9a71`.

Scope: parallel read-only mathematical/source review followed by a planning
update. No Lean file, theorem statement, axiom gate, or `sorry` changed.
The whole-project target remains constructive continuum Yang--Mills on R^4,
with the required QFT properties and positive finite physical mass for each
compact simple gauge group. This review proves no new analytic estimate.

## Finding that changes the plan

The signed fundamental-plaquette energy floor has an exact sector consumer,
but that sector is not the observable class quantified by the full Wilson
gap theorem. An upper variance estimate on unpropagated plaquette sums does
not yet supply iteration or full coverage.

| Declaration | Source | Consequence for the route |
| --- | --- | --- |
| `BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.family_energy_floor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174` | Original normalized temporal energy lower bound for signed fundamental spatial plaquette sums. |
| `BF4ExactSlabFixedSpatialClearedCovariance.clearedDefect_diagonal_nonnegative_iff` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175` | A same-marginal variance upper bound combines with that floor only for the observables actually bounded. |
| `BF4ExactSlabFixedSpatialWilsonWindow.WindowExpression` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindow.lean:50` | The syntax includes witnessed loops, arbitrary spins, offsets, products and signed linear combinations. |
| `BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.evenMoment_dyadic` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.lean:181` | States M(k)^2 <= M(2k)*M(0); it does not propagate an upper first-step bound forward. |
| `BF4ExactSlabFixedSpatialWilsonDenseGap.evenMoment_le_geometric` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonDenseGap.lean:76` | Supplies geometric control at every even time for every intrinsic expression, under the existing guards. |
| `BF4ExactSlabFixedSpatialWilsonDenseGap.evenMoment_first_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonDenseGap.lean:86` | Uses the all-time estimate and dyadic inequality to remove the expression-dependent prefactor. |
| `BF4ExactSlabFixedSpatialWilsonDenseGap.dense_unitComplement_twoStep_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonDenseGap.lean:112` | Bounds every intrinsic expression orthogonal to the actual unit, not only elementary faces. |
| `BF4ExactSlabFixedSpatialWilsonCompletedGap.completed_twoStep_form_gap` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonCompletedGap.lean:157` | Completed same-carrier two-step conclusion, retaining the existing small-nome hypotheses. |

Fundamental-plaquette-span transfer invariance or density of fundamental
plaquette time orbits in the full Wilson carrier: **NOT FOUND** in the
reviewed `BF4ExactSlabFixedSpatialTransferStep`,
`BF4ExactSlabFixedSpatialWindowPairing`,
`BF4ExactSlabFixedSpatialSeparatedWindowPins`,
`BF4ExactSlabFixedSpatialSeparatedCovariance`,
`BF4ExactSlabFixedSpatialWilsonWindow`,
`BF4ExactSlabFixedSpatialWilsonDenseGap` and
`BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments` modules under
`lean/YMGap/Continuum/`. This is a search boundary, not a nonexistence theorem.

## Actual iterated objects and first-step test

`BF4ExactSlabFixedSpatialTransferStep.transferStep`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferStep.lean:51`,
is the original step integrating K(x,y)V(x)f(x).
`swept_step_pairing` in the same module at line 77 pins its original
two-endpoint action. It is not pure product heat acting on f.

`BF4ExactSlabFixedSpatialWindowPairing.observedMessage`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean:48`,
contracts an actual finite observed window. `window_unobserved_pin` at
line 61 identifies its unit insertion with g_(m+L)=T^(m+L)(1).
`SU2QuaternionHeadWindowContraction.windowMessage_iterate`,
`lean/YMGap/Continuum/SU2QuaternionHeadWindowContraction.lean:201`,
retains the complete source polynomial in that contraction.

`BF4ExactSlabFixedSpatialSeparatedWindowPins.separatedMessage`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedWindowPins.lean:53`,
is T^r of the observed message. `separatedMessage_one` at line 69 pins its
unobserved partner to g_(m+L+r). `separatedPartition_eq` at line 82 keeps
the same total chain and partition.

Thus the existing pair to estimate is

    (T^r observedMessage(m,L,p), T^r g_(m+L)).

For a one-slice fundamental insertion, the first test is
`(T(g_m*chi_p), T(g_m))`. These are polynomial messages. Interpreting only
the first message as the original observable loses its unobserved partner.
No rational function needs to be introduced into the polynomial algebra.

`BF4ExactSlabFixedSpatialSeparatedCovariance.separated_input_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedCovariance.lean:54`,
already bounds the connected input ratios under a common partition.
`windowRatio_covariance_bound` at line 95 identifies the actual connected
window expectation. The rate is `mixRate(w,width)^r`, independent of boundary
depths and late cutoff but not width. Direct width-uniform promotion of
that computed rate is excluded by
`BF4ExactSlabFixedSpatialRateWidthObstruction.no_width_uniform_computed_rate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:132`.
This does not exclude a sharper actual correlation estimate.

The energy route already retains this difficulty:
`BF4ExactSlabFixedSpatialClearedCovariance.combinedTest`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:71`,
contains Tg, T(g*s), and the same-marginal mean correction.
`terminalResidual_clearedDefect` at line 158 is the full-source conditional
determinant. Repackaging these declarations supplies no improved estimate.

## Limiting-form guard is a separate prerequisite

`BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:99`,
and `intrinsicFormCauchy` at line 106 use the small-nome guards declared at
lines 93--96. A new finite-regulator decay estimate on an improved coupling
domain cannot instantiate that form outside its guards. The required
same-theory limit control must also be established on the improved domain.

## Bounded local calculation reviewed, not promoted to the main path

`SU2QuaternionHeatCovarianceRates.radialRate_factorization`,
`lean/YMGap/Continuum/SU2QuaternionHeatCovarianceRates.lean:34`,
and `radialRate_le_twentyFour_quadratic` at line 111 control the scalar
radial rate. `SU2QuaternionAdjacentPlaquetteHeat.adjacent_shared_defect`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteHeat.lean:326`,
retains two shared-link channels with a source-independent spectator.
Neither declaration bounds the complete source-dependent weight V*g_n.

A spectator-weighted own-face calculation is available as a short prospective
sublemma from `BF4ExactSlabSingleLinkCharacterSelection.original_character_local_zero`,
`lean/YMGap/Continuum/BF4ExactSlabSingleLinkCharacterSelection.lean:78`,
and `BF4ExactSlabAllExtentFaceHeatTail.faceHeatPolynomial_eq_sum`,
`lean/YMGap/Continuum/BF4ExactSlabAllExtentFaceHeatTail.lean:73`.
It has not been implemented or counted as proved by this audit. Even an
own-face diagonal variance upper bound would not supply the two polynomial
positivity certificates consumed by
`BF4ExactSlabFixedSpatialInputCovariance.inputCovariance_bracket_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialInputCovariance.lean:121`.
Accordingly no new isolated moment or comparison compiler is added here.

## Execution decision and verification boundary

Primary: find an original-action estimate that survives the first transported
pair and extends to the iterated Wilson-message family. The desired common
rate may depend on coupling; an explicit observable-dependent prefactor is
allowed, provided its time/regulator dependence supports the chosen limits.
Do not impose an unnecessary all-bare-coupling or coefficient-norm theorem.
The existing bracket proof is one possible producer, not a requirement to
prove a stronger pointwise estimate when a signed integrated determinant
bound would suffice.

Secondary: keep the proved plaquette-family energy floor and seek its
susceptibility upper input only when a demonstrated transfer/coverage join
makes that branch useful. Retain all transverse/source-dependent terms.

No improved width-uniform transferred-pair estimate was found in the cited
sources or proved here. Same-theory continuum/QFT, physical calibration and
all compact simple groups remain open. Existing small-nome completed gap and
excitation are preserved. Verification for this checkpoint is source and
documentation review only; independent mathematical review passed and its
six line-reference corrections were applied. No Lean build or axiom audit
was run.
