# The original transfer gap reaches the existing series core

Date: 2026-09-30 UTC. Classification: PROGRESS. Clay target remains OPEN.

## Short argument, actual objects

T is the existing all-nome completed Wilson one-step time operator. Its
constructed series is F=sum_(k>=1)(I-T)^k*T/k. The existing witnessed graph
has core pairs (T x,F x); neither an inverse of T nor a different carrier is
introduced here.

Write q for the existing two-step form rate, equivalently the one-step
squared-norm rate. On the original vacuum complement, positivity of
||x-Tx||^2 and ||Tx||^2<=q||x||^2 gives

    <x,(I-T)x> >= (1-q)/2 * ||x||^2.

All terms in the actual series paired with T x are nonnegative. Its first
term therefore gives

    <T x,F x> >= <T x,(I-T)T x> >= (1-q)/2 * ||T x||^2

when T x is vacuum-orthogonal. The margin is positive at each strict nome
and fixed width, but still depends on both parameters.

## Checked declarations

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `logPartial_time_firstTerm_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogRangePositive.lean:123` | First-term lower bound for every nonempty finite partial sum. |
| `regularizedLog_time_firstTerm_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogRangePositive.lean:161` | Same lower bound for the actual represented series limit. |
| `coreMargin`, `coreMargin_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:52`, `:55` | Explicit positive rational margin (1-q)/2. |
| `completed_defect_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:101` | Strict one-step defect form on the existing vacuum complement. |
| `core_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:122` | The displayed strict bound on the actual graph core. |
| `regularizedLog_zero_iff_time_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:130` | F x=0 iff T x=0 for vacuum-orthogonal x. |
| `graph_input_time_kernel_eq_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:151` | A witnessed graph input in ker(T) is zero. |
| `graph_zero_output_iff` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:172` | On the vacuum complement, zero graph output iff zero input. |
| `action_zero_iff_input_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:186` | Same statement on the existing quotient graph domain. |
| `plaquette_regularizedLog_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:196` | An actual active plaquette supplies a nonzero series output. |

For graph-kernel control, use `graph_time_pin` to get T(output)=F(input).
Zero output and vacuum orthogonality imply T(input)=0 by the new core result.
The graph's supplied approximants T(source_n) are then orthogonal to input.
Their explicit convergence modulus forces the input norm to vanish. This
does not assume a norm bound for the preimages source_n.

The original boundary time kernel remains present in the unchanged carrier.
The graph-input conclusion follows from a theorem about its approximants,
not a quotient that removes those states.

## Relation to the analytic frontier

This is an independent reconstruction join with already constructed inputs.
It does not replace the missing same-source relative temporal-energy UPPER
estimate needed by the scaling-survival branch. Source review found only
two-loop mixed upper bounds, not a useful whole-family scaling estimate.

The checked family temporal-energy LOWER floor also prevents a free
gradient-only cancellation argument at fixed nome: constant coefficients
have zero interior coefficient gradient but positive coefficient-square
budget. Any proposed estimate must retain appropriate zeroth-order/boundary
terms or prove source-specific variance amplification. No new Lean
asymptotic obstruction is claimed by this planning observation.

## Remaining obligations

The quantitative bound above is on the core, not yet the entire witnessed
graph. The full graph result here is a kernel statement, which alone is not
a spectral gap. Passing the universal first-term/defect-form inequality
through graph limits is the next available reconstruction step.

Scalar-log identification, density in the appropriate physical sector,
self-adjointness, continuous physical time, spatial/spacing calibration,
continuum nontriviality and all Clay fields remain OPEN. No formal frontier
type was weakened or newly inhabited.

## Verification

Two serialized focused checks passed 13 printed gates (11 new and two
existing), all within {propext, Quot.sound}. The safe launcher used one
worker, the mandatory 20 GiB ceiling and 12 GiB OS reserve. No full root,
full-tree build, audit or guard was run. No new sorry, axiom or classical
dependency. The canonical chart is unchanged and is not reprinted.

- `/tmp/ym-log-first-term-20260930.log`, SHA-256:
  `6ef15a6d4ed2131771f697a0845ebf6e87b6dc13b041978c6f1be8c4cc6b48e2`
- `/tmp/ym-log-core-gap-20260930.log`, SHA-256:
  `869b358fb8d14e9cdc2ab3362f8cc8d21653c5de0624b5e206718ac4e27600a1`
