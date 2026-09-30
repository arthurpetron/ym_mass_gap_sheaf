# All-nome time-zero observables on the original reflected completion

Date: 2026-09-30 UTC. Parent baseline: `9bf84e1`.

## Mathematical increment

For every rational nome `0<w<1`, fixed literal width, supplied spatial loop
and spin index, multiplication by its time-zero character now acts on the
EXISTING `BF4WilsonAllNomeCompletedInner.Completion`. The squared-norm
bound is `B(Mx,Mx) <= characterBound(spin)*B(x,x)`. It is a reflected
norm bound, not an ordinary-Haar replacement. At fundamental spin index 1
the cap is four. The bound is independent of nome, width and input state;
the underlying carrier and functional still depend on nome and width.

The finite argument retains the entire selected action and its partition:
reflection fixes the inserted character `a`, and positivity of the certified
fixed-slice weight `c-a*a` implies `Q(a*p)<=c*Q(p)`. The original joint
cutoff/time limit preserves this inequality. Applying it to differences
constructs the completed map with input tolerance `epsilon/(c+1)`.

## Source-to-consumer map

| Declaration | Source | Role |
| --- | --- | --- |
| `selectedAction_multiplier_bound` | `lean/YMGap/Continuum/BF4ExactSlabSiteMultiplierBound.lean:119` | Existing exact original-action numerator estimate. |
| `originalWindowScalar_timeZero_multiplier_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroBound.lean:113` | New literal-width normalized finite bound, with the same partition. |
| `commonForm_timeZero_multiplier_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroBound.lean:171` | Actual joint-limit reflected-form bound. |
| `intrinsicForm_multiplier_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroBound.lean:195` | Same intrinsic form, with no small-nome guards. |
| `intrinsicForm_multiplier_balance` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroBound.lean:245` | Reflection-fixed insertion moves between the form's two entries. |
| `distSq_multiplier_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroBound.lean:294` | Same original squared-distance bound. |
| `multiplierContinuous`, `multiplyCauchy_modulus` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:53`, `:71` | Explicit tolerance and representative modulus, without choice. |
| `completedMultiply`, `completedMultiply_embed` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:77`, `:86` | Actual map on the existing completion; exact dense action. |
| `completedInner_multiplier_balance` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:120` | Symmetry on every completed state. |
| `completedMultiply_add`, `completedMultiply_smul`, `completedMultiply_realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:132`, `:140`, `:148` | Linearity, retaining constructive-real modulus data. |
| `completedInner_multiplier_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:159` | Spin-only cap on every completed vector. |

`completedMultiply_unitState` in
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroVacuum.lean:109`
identifies the fundamental multiplier of the existing unit with the
already embedded literal loop state. `completedMultiply_unitState_lag`
in `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroVacuum.lean:119`
identifies its SAME completed-time autocorrelation
with the original `lagMoment`. Thus the new map has an actual original-law
consumer, not merely an abstract bounded-map interface.

## Same-object checks and scope

The earlier `chartScalar_original_pin` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:127`
uses `centeredExpression r` at a padded width EVEN when `r=0`. It was not
treated as an identity with the literal-width all-nome form. The new proof
instead instantiates the selected action directly at the literal width.
Only parameter-free syntax and tolerance arithmetic are reused from the
small-nome multiplier modules; their spatial-limit forms are not reused.

This supplies actual observables on the current fixed-width construction,
an independent partial J02 result. It does not construct cross-width maps,
spacing limits, continuum locality, a Hamiltonian, new strict decay, or a
useful original signed/collective scaling estimate. A03 and full J02 remain
open. The canonical chart block and all Clay status markers are unchanged.

Parallel consumer review also rejected spending this turn on a sharper
ordinary-heat `w^6` bound: its original finite consumer
`centered_transfer_square_bound` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredKineticBound.lean:94`
still has `H[(V F)^2]` on the right, not the needed interacting variance.
Existing finite reflected completions were found, so no duplicate generic
GNSData wrapper was added.

## Verification

All three new modules passed focused serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20` with
their own `--check` and `--check-output` paths. All 25 printed gates
reported only `{propext, Quot.sound}`. A first dense check found one
extra proof argument; the vacuum pin required namespace, reflexivity and
dependent-rewrite repairs before its successful check. No limits were raised.
No new sorry, analytic premise or axiom was introduced. No broad build,
full audit, numerical certificate search or concurrent compiler ran.

Sol implemented the direct dense bound and balance. The main agent constructed
the completed map and linear laws. Luna reviewed the completion scope and
implemented the vacuum pin; the main agent repaired its last elaboration
issues. All compilation was serialized by the main agent. One initial
vacuum check outlasted its initial call; it was checked manually only after
about five minutes while source and downstream-consumer review continued.
Automatic memory protection stayed active. All final successful checks
finished in their initial calls.
