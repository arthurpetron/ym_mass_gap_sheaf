# The original transfer gap reaches the existing witnessed series graph

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

## Follow-on: exact margin on the entire witnessed graph

The next step is now proved, not an assumed continuity premise. For every
existing `GraphLimit` witness (x,y), its input images a_n=T(source_n) and
output images F(source_n) approximate x and y with the supplied modulus.
Distance-one control bounds ||a_n||^2 by 2+2*c when ||x||^2<=c. Time
contraction then permits ordinary pairing continuity for both B(a_n,a_n)
and B(a_n,T a_n). Together with the existing graph-pairing modulus this passes

    B(a_n,(I-T)a_n) <= B(a_n,F(source_n))

to B(x,(I-T)x)<=B(x,y). Neither bounded preimages nor their chosen Cauchy
representatives are required. Applying the already checked defect gap to x
gives the SAME full margin (1-q)/2 on every vacuum-orthogonal graph input.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `graphInputPairingModulus` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:89` | Explicit all-tail input-pairing cutoff from the original graph modulus and supplied norm cap. |
| `graph_input_pairings_close` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:96` | Both order errors for the norm and one-step pairing along graph input images. |
| `graph_defect_form_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:133` | Universal defect-form lower bound on every existing witnessed graph pair. |
| `graph_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:174` | Full original margin for vacuum-orthogonal graph input. |
| `action_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:182` | Same quantitative bound on the existing quotient domain and action. |

## Remaining obligations

Scalar-log identification, density in the appropriate physical sector,
self-adjointness, continuous physical time, spatial/spacing calibration,
continuum nontriviality and all Clay fields remain OPEN. No formal frontier
type was weakened or newly inhabited.

The next same-object reconstruction requirement is a fractional-time calculus
for this original all-nome T, strongly continuous on the closure of its
positive-time range, plus the explicit core limit
(T x-T^s T x)/s -> F x and a graph-core identification. The existing
`BF4ExactSlabThermodynamicDyadicSemigroup.action_one`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicSemigroup.lean:132`,
is pinned to that OTHER carrier's two-step transfer, not this T. No bridge
is supplied by the present result. The nonzero original time kernel prevents
assuming strong continuity on the whole carrier merely from positive-time
power laws.

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

Follow-on verification: one further focused capped check passed the five new
graph-gap gates within {propext, Quot.sound}; no full-tree check or canonical
chart change. Log `/tmp/ym-log-graph-gap-20260930.log`, SHA-256:
`0a9afb9c9e1faf8c5e99cf91be1c6a77137e09e4443c6a30c7a6e3dd801c78b3`.
