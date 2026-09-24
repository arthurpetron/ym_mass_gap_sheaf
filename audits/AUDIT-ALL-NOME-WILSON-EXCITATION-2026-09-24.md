# Nonzero excitation on the SAME all-nome Wilson completion — 2026-09-24

## Outcome and scope

Baseline: `83acacc`. For every rational nome `0<w<1`, every positive spatial
width now has a constructed nonzero centered plaquette vector in the EXISTING
literal-width Wilson completion. Its squared norm is at least the computed
positive `starRatio(w)`, independent of width and face position. At every
width at least two, an explicit strictly padded plaquette also has a positive
one-step response, with a supplied nome/width-dependent rational floor.

These are actual vectors, not scalar nontriviality claims awaiting a carrier.
Their connected moments are matrix coefficients of the SAME temporal map
that satisfies the previously proved strict two-step bound. No face-span
completion or older small-nome Wilson carrier is substituted.

The literal changing-scale Wilson squares also have constructed centered
vectors and the SAME absolute loss bound `384*L^3*(1-w)`. No positive norm
floor for that growing-loop family or justified scaling survival is proved.

## Constructive joins and exact consumers

1. `BF4WilsonAllNomeCenteredVector.centerApprox_distance`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:105`) proves the
   squared distance of two rational centerings is `(q-r)^2`. `centeredRate`
   (`:115`) consumes the actual mean's `intrinsicFormCauchy` modulus.
   `centeredStream` (`:118`) and `centeredVector` (`:129`) construct the
   Cauchy stream and its class, with no choice of representative.
2. `centeredVector_orthogonal` (`:147`) and `centeredExcitation` (`:152`)
   place the vector in the EXISTING
   `BF4WilsonAllNomeCompletedTime.VacuumComplement`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:171`).
   `centeredVector_time_pairing` (`:159`) and `centeredVector_diagonal`
   (`:167`) identify its actual autocorrelation and norm with the original
   `centeredTimeMoment`; these are equalities, not assumed pins.
3. `BF4WilsonAllNomePlaquetteVariance.literal_mean_pin`
   (`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteVariance.lean:95`) pins the
   literal Wilson mean directly to the original zero-window expectation.
   `mean_pin` (`:112`) compares the old face scalar through the SAME finite
   source/partition, without comparing completed carriers.
   `centered_norm_pin` (`:153`) joins this mean pin with the existing exact
   lag-zero pins; `centered_norm_floor` (`:171`) consumes
   `BF4ExactSlabFixedSpatialLocalVariance.face_joint_variance_floor`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalVariance.lean:111`).
4. `BF4WilsonAllNomePlaquetteExcitation.plaquetteExcitation`
   (`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteExcitation.lean:53`) is the
   explicit centered plaquette. `plaquetteExcitation_norm_floor` (`:60`),
   `plaquetteExcitation_norm_ne_zero` (`:66`), and
   `plaquetteExcitation_ne_zero` (`:78`) prove quantitative nontriviality
   against the actual embedded zero. `nonzeroExcitation` (`:113`) returns
   the vector and proofs in Type for every positive width; `originFace_mem`
   (`:107`) discharges the face-existence requirement constructively.
5. `plaquetteExcitation_correlator_pin` (`:85`) and
   `plaquetteExcitation_twoStep_bound` (`:90`) retain the SAME vector,
   completed pairing and time operator. `centered_response_floor`
   (`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteVariance.lean:178`)
   consumes the existing
   `BF4WilsonAllNomePlaquetteConnectedFloor.connected_response_floor`
   (`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteConnectedFloor.lean:136`).
   `plaquetteExcitation_response_floor`
   (`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteExcitation.lean:98`)
   makes it an actual completed matrix coefficient. `positiveResponseExcitation`
   (`:123`) returns both state and positive rational floor. The active-link
   premise is PROVED by `plaquette_active_after_padding`, not added as an
   analytic hypothesis to this witness.
6. `centeredVector_loss_pin`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:175`) cancels
   the SAME mean correction from time loss for every intrinsic expression.
   `centered_dyadic_loss_bound` (`:194`) transfers the existing geometric
   loss bound to the actual centered square vector. The cubic cost and
   absence of a growing-loop norm comparison are unchanged.

## Parameter audit and the failed certificate join

The norm floor is `BF4ExactSlabLocalStarComparison.starRatio`
(`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:46`): the sixth
power of `localFloor(w)` divided by the sixth power of `localCap(w)`.
It depends on nome, not width, face position, late cutoff or terminal depth.
The positive response floor is
`BF4ExactSlabFixedSpatialPlaquetteUniformResponse.uniformFloor`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteUniformResponse.lean:98`),
with positivity at `:103`. Its uniformity concerns cutoff/depth at FIXED nome
and width; it is not uniform in coupling or width. Neither constant supplies
a physical-spacing trajectory or cross-scale identification.

`BF4ExactSlabStarVarianceLossObstruction.starRatio_le_defect_power`
(`lean/YMGap/Continuum/BF4ExactSlabStarVarianceLossObstruction.lean:38`)
proves `starRatio(w) <= ((1-w)*(1-w))^6`. Its
`starRatio_le_nome_defect` (`:54`) and
`starRatio_sub_mul_nome_defect_nonpositive` (`:78`) imply that subtracting
`C*(1-w)` from this floor is nonpositive for every `C>=1`.
`plaquette_budget_nonpositive` (`:93`) specializes to `C=192`, half the
four-edge one-step increment budget in
`BF4WilsonAllNomeTimeIncrement.timeIncrement_nome_bound`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTimeIncrement.lean:120`).

This is a limitation of the AVAILABLE certificate pair. It is NOT an upper
bound on actual variance, a lower bound on actual loss, or a refutation of
positive response. The independently proved positive one-step response above
illustrates the distinction. Do not confuse this six-face certificate with
the older, different 24-face affine comparison floor.

## Next causal frontier and chart contract

Useful SAME centered variance/response control on a justified changing-scale
observable/coupling/width/spacing trajectory remains the analytic frontier
A03. The new actual centered square consumer makes that comparison meaningful
on this completion; its required estimate is still missing. The plaquette
certificate obstruction rules out using these coarse bounds alone to supply
it. A fixed-nome positive response and pointwise strict upper rate do not
establish nonzero response at a fixed physical time as spacing changes.

Spatial/spacing control of EVERY-state decay is a separate open input.
Full metric/Hilbert/OS/QFT structure, SAME continuum/YM/UV construction,
physical Hamiltonian/mass and every compact simple group remain open. The
old face-span survival theorem is not imported as a Wilson-carrier theorem.

Schema 1, snapshot 12 records partial A03/J02 evidence only. The canonical
chart block, labels, layout, proof markers, A03 frontier and B01--B03's
recorded face-span scope are unchanged. No canonical field is closed or
weakened; no additional frontier bundle is introduced.

## Verification boundary

Four final narrow checks exited 0 through `scripts/safe_lean_build.py`, with
one worker, explicit `.olean` output, 2 GiB worker cap, default elaboration
limits and the unchanged 12 GiB reserve. All 33 printed gates are within
`{propext, Quot.sound}`; `originFace` has no axiom dependency.

| Leaf | Final log in `/tmp/` | Printed gates |
|---|---|---:|
| CenteredVector | `ym-gap-wilson-all-nome-centered-vector-check-4.log` | 12 |
| PlaquetteVariance | `ym-gap-wilson-all-nome-plaquette-variance-check-2.log` | 5 |
| PlaquetteExcitation | `ym-gap-wilson-all-nome-plaquette-excitation-check-3.log` | 11 |
| StarVarianceLossObstruction | `ym-gap-star-variance-loss-obstruction-check-3.log` | 5 |

The pending draft's initial centered-vector check was safety-stopped; a later
launch was refused at preflight. Verification resumed after recovery, without
reducing the reserve, raising limits, or stopping user processes. Intermediate
checks exposed namespace, notation, explicit-argument and Type-packaging
errors; these were corrected before the listed final checks. There is no
source `sorry`, new axiom, classical dependency or new analytic premise.

Independent bounded source review checked the actual-carrier joins and the
certificate/physical-bound distinction. Two semantic-root imports are added;
no full-root build, full-tree audit, guard or broad progress suite was run.
CI remains unchanged. The verification claims concern these named leaves,
not a fresh whole-repository audit.
