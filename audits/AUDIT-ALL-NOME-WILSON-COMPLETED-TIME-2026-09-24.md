# Literal all-nome Wilson completion and actual time — 2026-09-24

## Scope and outcome

Baseline: `76e9046`. The actual literal-width all-nome reflected Wilson form
now supplies a represented Cauchy completion, its explicit-modulus pairing,
and the actual positive contractive discrete-time semigroup. The embedded
unit has norm one and is fixed; its orthogonal sector is invariant. Original
Wilson lag moments and the dyadic absolute loss bound are matrix coefficients
of this SAME completed operator. No new analytic hypothesis is supplied.

This is partial J02 progress. It is not the separate face-span completion or
the older small-nome/spatial-limit Wilson completion. It does not establish
full Hilbert/QFT structure, a strict gap on this carrier, nonconstant survival,
physical scaling or the continuum/Clay target. Canonical schema 1, snapshot 10
changes evidence only; the chart fence and all node markers remain unchanged.

## Causal proof and exact consumers

1. `BF4WilsonAllNomeFormLaws.intrinsicForm_sum_left`,
   `.intrinsicForm_difference_diagonal`, and `.intrinsicForm_unit_unit`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeFormLaws.lean:105`, `:165`, `:191`)
   prove rational algebra and normalization of the existing original form.
   They retain only the strict nome guards, literal width and actual intrinsic
   expression. The older ordinary-CS module supplies `joint_smul` algebra,
   not an alternative pairing.
2. `BF4WilsonAllNomeCauchySchwarz.intrinsicForm_cauchySchwarz` and
   `.intrinsicForm_radical_zero`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCauchySchwarz.lean:171`, `:225`)
   derive sharp CS from the actual reflected finite form and joint limits.
   `BF4WilsonAllNomeSeminorm.seminorm`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeSeminorm.lean:151`) uses the
   literal difference, proved squared triangle law and null congruence.
3. `BF4WilsonAllNomePairingContinuity.pairing_close` and
   `.diagonal_anchor_bound`
   (`lean/YMGap/Continuum/BF4WilsonAllNomePairingContinuity.lean:89`, `:123`)
   supply the existing generic completion API with proved quantitative data.
   `BF4WilsonAllNomeCompletedInner.intrinsicFormCauchy` and `.pairingData`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedInner.lean:43`, `:53`)
   retain the actual joint-limit approximation modulus as data, rather than
   extracting it from a propositional Cauchy field.
4. `BF4WilsonAllNomeCompletedInner.Completion`, `.completedInner`,
   `.completedInner_cauchySchwarz`, and `.unitState_norm_one`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedInner.lean:59`, `:64`,
   `:82`, `:90`) construct the represented quotient and pairing.
   `.completed_loop_time_pairing` (`:98`) retains the exact two-time pin.
   Generic completion machinery is reused only after its quantitative inputs
   have been proved on this specific reflected form.
5. `BF4WilsonAllNomeTimeForm.intrinsicForm_time_sum` and
   `.intrinsicForm_oneStep_nonnegative`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeForm.lean:44`, `:99`) prove
   balance and positivity from the SAME original joint windows. The one-step
   identity uses the already-positive odd window and exterior time padding;
   it does not enlarge spatial width.
6. `BF4WilsonAllNomeTimeContraction.originalWindowScalar_abs_bound` and
   `.originalJointLimit_approx_abs_bound`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeContraction.lean:59`, `:69`)
   bound actual finite expectations and every joint-limit approximation by
   the observable interval cap. The cap is unchanged by time advance.
   `.timeNorm_le_anchor` (`:152`) applies bounded midpoint doubling to this
   cap, time balance and difference positivity. It removes the prefactor
   without dividing by a possibly zero norm. `.distSq_advance_contraction`
   (`:167`) proves actual advance nonexpansive on the SAME seminorm.
7. `BF4WilsonAllNomeCompletedTime.completedTime`, `.completedTime_add`,
   `.time_cauchy_modulus`, and `.completedUnit_fixed`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:73`, `:82`,
   `:93`, `:139`) descend actual advance, prove the semigroup law, retain
   the supplied outer modulus, and fix the unit. `.VacuumComplement` and
   `.completedTime_preserves_vacuumComplement` (`:171`, `:173`) specify and
   preserve orthogonality on this carrier. They do not assert an excited
   vector or isolate the unit from the remaining spectrum.
8. `.completedInner_time_balance`, `.completedInner_time_contraction`, and
   `.completedInner_oneStep_nonnegative` (`:164`, `:191`, `:205`) hold for
   every represented completed vector. `.completedTime_loop_lag` (`:212`)
   identifies the actual completed matrix coefficient with the original lag.
   `.completed_dyadic_loss_bound` (`:221`) is its geometric consumer:

   `2*(B(x,x)-B(x,T(L)x)) <= 384*L^3*(1-w)` for the embedded square of side L=2^s.

   This remains an absolute estimate. It contains no centered-variance floor
   or justified relation between nome, width and physical spacing.

## Remaining join and reviewed next frontier

The separate `BF4ExactSlabFixedSpatialJointCompletedGap.completed_twoStep_form_gap`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCompletedGap.lean:150`)
has type on `JointCompletion`, not the newly constructed Wilson completion.
An embedding of the old face-generated carrier would transport that estimate
only to its image; this milestone proves neither such an embedding nor
density/surjectivity in the arbitrary-loop Wilson carrier.

The next candidate is direct centered physical-lag control for every
`IntrinsicExpression width`. The existing
`BF4ExactSlabFixedSpatialSeparatedCovariance.polynomialWindow_covariance_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedCovariance.lean:117`)
already accepts arbitrary supported polynomials. The old face-span consumer
`BF4ExactSlabFixedSpatialPhysicalCovariance.connectedScalar_abs_le`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPhysicalCovariance.lean:175`)
uses separated reflected-product and marginal identities to apply it.
Analogous SAME-Wilson source identities and the centered lag envelope are
not established by the present milestone. They are the next proof task,
not an assumption added to the new completion.

Full represented metric/Hilbert/OS/QFT assembly, useful SAME centered
variance/nonzero response on a justified scaling family, EVERY-state decay
under scaling, continuum/YM/UV structure, physical Hamiltonian/mass and every
compact simple group remain open. The unit norm and a contractive semigroup
alone prove none of those conclusions.

## Verification boundary

Each final check used the repository safe launcher, `--jobs 1`, `--check`,
an explicit `.olean` output and `--check-worker-limit-gib 2`. Default Lean
elaboration limits and the 12 GiB OS reserve were unchanged. All eight final
processes exited 0. All 67 printed gates are within `{propext, Quot.sound}`;
`intrinsicCap` is axiom-free.

| Leaf | Final log in `/tmp/` | Gates |
|---|---|---:|
| FormLaws | `ym-gap-wilson-all-nome-laws-check-2.log` | 16 |
| CauchySchwarz | `ym-gap-wilson-all-nome-cs-check-2.log` | 2 |
| Seminorm | `ym-gap-wilson-all-nome-seminorm-check-1.log` | 8 |
| PairingContinuity | `ym-gap-wilson-all-nome-continuity-check-1.log` | 4 |
| TimeForm | `ym-gap-wilson-all-nome-time-form-check-6.log` | 4 |
| CompletedInner | `ym-gap-wilson-all-nome-completed-inner-check-1.log` | 9 |
| TimeContraction | `ym-gap-wilson-all-nome-time-contraction-check-1.log` | 8 |
| CompletedTime | `ym-gap-wilson-all-nome-completed-time-check-2.log` | 16 |

The safe launcher refused one TimeForm launch at 11.3 GiB available and
stopped another at 11.4 GiB, honoring the reserve. Process/memory inspection
confirmed recovery before the final retry. No user process was stopped and
no safety limit was relaxed. Namespace/notation mistakes and excessive
joint-limit unfolding in development drafts were repaired; no source
`sorry`, classical dependency or new axiom was introduced.

Independent bounded source review confirmed the original action, literal
width and all-nome scope. One semantic-root import was added. A full-root
build, full-tree audit, guard or progress suite was NOT run; these focused
checks do not claim repository-wide verification. CI remains unchanged.
