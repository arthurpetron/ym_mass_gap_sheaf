# Strict bound on the SAME all-nome Wilson completion — 2026-09-24

## Outcome and scope

Baseline: `9d61414`. For every rational nome `0<w<1`, fixed natural spatial
width, and EVERY vector x orthogonal to the embedded unit in the existing
literal-width Wilson completion, the original temporal semigroup satisfies

`B(x,T(2)x) <= q(w,width)*B(x,x)`, with computed `0 <= q(w,width) < 1`.

The precise declaration is
`BF4WilsonAllNomeCompletedGap.completed_twoStep_form_gap`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:146`). The carrier
is `BF4WilsonAllNomeCompletedInner.Completion`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedInner.lean:59`), the pairing
is that module's `completedInner` (`:64`), and time is
`BF4WilsonAllNomeCompletedTime.completedTime`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:73`).

This is a fixed-parameter form bound, not a continuum Hamiltonian gap. No
nonzero excitation, spatial/spacing-uniform estimate, full Hilbert/OS/QFT
structure, physical mass or all-group construction is supplied. No new
analytic hypothesis, bridge assumption or alternative carrier is introduced.

## Causal proof and consumers

1. `BF4WilsonAllNomeSeparatedCovariance.originalWindowScalar_centered_abs_le`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeSeparatedCovariance.lean:128`)
   compares the actual reflected joint insertion and BOTH unit marginals
   with two fixed polynomials separated by the physical lag. The same
   original action, cutoff, terminal depth, partition and width are retained.
   Its input is the existing proved
   `BF4ExactSlabFixedSpatialSeparatedCovariance.polynomialWindow_covariance_bound`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedCovariance.lean:117`),
   not an assumed decay field. `.intrinsic_centered_covariance_le` (`:222`)
   passes the estimate through the witnessed original joint limits.
2. `BF4WilsonAllNomeCenteredMoments.centeredTimeMomentCauchy`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredMoments.lean:46`) retains
   explicit scalar approximation data. `.centeredApprox_time_converges`
   (`:120`) uses rational approximations to the actual constructive-real
   unit coefficient. No completed real-linear centering operation is assumed.
   `.evenMoment_nonnegative`, `.evenMoment_le_zero`, and `.evenMoment_dyadic`
   (`:178`, `:184`, `:190`) derive the even-moment laws on this SAME form.
3. `BF4WilsonAllNomeDenseGap.evenMoment_first_le` and `.centered_twoStep_bound`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeDenseGap.lean:71`, `:111`)
   use the geometric envelope and dyadic inequality to remove the
   expression-dependent prefactor. The rational zero-rate case is included;
   there is no division by a possibly zero norm or positive-norm hypothesis.
4. `BF4WilsonAllNomeCompletedGap.representativeCenteredMomentCauchy` and
   `.representativeCenteredMoment_converges`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:53`, `:68`)
   use the three actual pairing limits of each supplied Cauchy representative.
   `.representative_twoStep_form_gap` (`:94`) passes the dense estimate to
   these limits. Quotient induction gives `.completedCenteredScalar_twoStep_gap`
   (`:104`), with no selected representatives or uniform presentation cap.
5. `.completedCenteredScalar_of_orthogonal` (`:138`) removes the mean
   correction when B(x,U)=0. `.completed_twoStep_form_gap` (`:146`) gives
   the actual completed bound. `.vacuumComplement_twoStep_form_gap` (`:165`)
   consumes the EXISTING `BF4WilsonAllNomeCompletedTime.VacuumComplement`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:171`), using
   pairing symmetry to match its stored orientation B(U,x)=0.

## Parameter and operator audit

- `separationCap` (`lean/YMGap/Continuum/BF4WilsonAllNomeSeparatedCovariance.lean:68`)
  is computed from the two literal polynomial caps and their common radius.
  It depends on the expressions (and their width), not on the physical lag
  or cutoff/boundary stage. The dense argument removes it from the final rate.
- `kineticFloor` and `kineticCap`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:57`, `:61`)
  are respectively `headFloor(w)^temporalFaces(width).length` and
  `prefixCap(w)^temporalFaces(width).length`. `mixFraction` is their exact
  positive quotient, and `mixRate=1-mixFraction`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferMixingRate.lean:81`,
  `:110`). `mixRate_nonnegative` and `mixRate_lt_one` (`:113`, `:124`)
  retain nome and width dependence while removing late-cutoff dependence.
- `twoStepRate`, `.twoStepRate_nonnegative`, and `.twoStepRate_lt_one`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:45`,
  `:48`, `:53`) supply the scalar square and its strictness. Only these
  scalar definitions/laws are reused from the old face-span dense-gap file;
  its carrier and form estimate are not transported.
- The operator is the completion of literal physical `advance`, by
  `timeNonexpansive` and `completedTime_embed`
  (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:53`, `:86`).
  It is not a link heat-bath dynamics. The previous
  `completedTime_loop_lag` (`:212`) remains the exact original-correlator pin.

No statement here supplies control of q as width or physical spacing changes,
or identifies a continuum generator. Pointwise q<1 does not supply those inputs.

## Remaining causal frontier and chart stability

The literal Wilson family still needs useful SAME centered-variance or
nonzero-response control on a justified coupling/width/spacing trajectory.
Its existing absolute loss estimate `384*L^3*(1-w)` does not supply that
comparison. A strict UPPER bound likewise supplies no positive norm floor.
The EVERY-state scaling estimate is a separate missing input. Full
metric/Hilbert/OS/QFT assembly, SAME continuum/YM/UV structure, physical
Hamiltonian/mass and every compact simple group remain open.

The face-span survival consumer is not automatically a Wilson-carrier
consumer. This milestone proves no isomorphism/density bridge between those
completions. It directly proves the strict bound on the intended Wilson one.

Canonical chart schema 1, snapshot 11 adds this evidence without changing
the fenced chart, node labels, status markers or primary A03 frontier.
The B01--B03 registry retains its recorded face-span interpretation; the
new Wilson result is separately recorded partial J02 evidence. No canonical
frontier field is changed or declared closed.

## Verification boundary

All four final focused checks exited 0 under `scripts/safe_lean_build.py`,
`--jobs 1`, explicit `.olean` output, and `--check-worker-limit-gib 2`.
Default elaboration limits and the 12 GiB OS reserve were unchanged.
All 33 printed gates report only `{propext, Quot.sound}`.

| Leaf | Final log in `/tmp/` | Printed gates |
|---|---|---:|
| CenteredMoments | `ym-gap-wilson-all-nome-centered-moments-check-1.log` | 12 |
| SeparatedCovariance | `ym-gap-wilson-all-nome-separated-covariance-check-2.log` | 6 |
| DenseGap | `ym-gap-wilson-all-nome-dense-gap-check-1.log` | 3 |
| CompletedGap | `ym-gap-wilson-all-nome-completed-gap-check-1.log` | 12 |

The unchanged CenteredMoments leaf was checked in the preceding proof turn;
its final log was reinspected before its checked interface was consumed.
The first covariance check found namespace and source-expression inference
errors, repaired before the final passing check. No source `sorry`, classical
dependency, new axiom or added analytic hypothesis is present. No safety
limit was raised and no user-owned process was stopped.

Independent bounded source reviews checked the completed consumer and the
rate/operator distinction. One semantic-root import was added. A full-root
build, full-tree audit, guard or broad progress suite was NOT run. CI is
unchanged. These checks certify the named leaves, not the entire repository.
