# Witnessed graph of the original regularized time series

## Goal and scope

Whole-project goal: constructive continuum Yang--Mills on R^4 for every
compact simple group, with same-theory QFT axioms, nontriviality and a
finite positive physical Hamiltonian gap. The goal remains OPEN.

This increment uses the EXISTING SU(2), all-nome, fixed-width completed
Wilson carrier, original discrete time T=T(1), and constructed bounded map

    F x = sum_{k>=1} (I-T)^k T x/k.

It constructs a single-valued graph from limits of the actual pairs
(T x,F x). The input carrier, original action, vacuum and boundary kernel
are unchanged. The notation does not assert F=T*(-log T), scalar functional
calculus, a physical Hamiltonian or continuous-time evolution.

## The short mathematical argument

A graph witness for (u,v) supplies a sequence x_n and ONE explicit modulus
for both squared distances ||T x_n-u||^2 and ||F x_n-v||^2. No bound on
||x_n|| is assumed. Nonexpansiveness and FT=TF imply T v=F u.

If u=0, then T v=0 and the existing kernel law implies F v=0. Symmetry
therefore gives B(v,F x_n)=0. Positivity implies

    ||v||^2 <= ||v-F x_n||^2 -> 0,

so v=0. Subtracting two witnesses gives uniqueness of the output for a
fixed input. This is closability of the actual core, not a bounded inverse
for T and not injectivity of T. Preimages may diverge in norm.

For a supplied sequence of graph witnesses converging with a supplied
outer modulus, select from witness n at its explicit tolerance 1/(n+1).
The maximum of the outer quarter-tolerance modulus and the denominator
of that quarter tolerance is a diagonal modulus. Thus witnessed sequential
graph limits flatten to a graph witness without countable choice.

Presentations contain input, output and the simultaneous convergence data.
Quotient them by equality of the ORIGINAL input. Uniqueness makes `action`
well-defined; `input` is injective. `fromTime x` has exactly input T x and
action F x. In particular the original vacuum is in the domain and has
zero action. No representative or preimage is selected from a quotient.

The positive core pairing B(T x,F x) follows termwise from the existing
mixed moments B(T x,(I-T)^k T x)>=0 and passes through the actual series
limit. Positivity of F alone is not substituted for this mixed statement.

Rational scaling preserves graph witnesses using tolerance e/(1+c*c).
Addition is subtraction of the negative witness. These constructions
descend to the quotient with exact linearity pins for input and action.
No full-real domain operation is asserted in this increment.

The form laws also extend to every witnessed graph pair. For two witnesses,
supplied rational norm ceilings cx,cv give
cap=max(cx,2+2*cv). The output's distance-one tail bounds its approximating
norm by that cap, without bounding source norms. The explicit
`graphPairingModulus` is the maximum of both graph moduli at the existing
pairing tolerance and the second output's distance-one cutoff. Two such
computed indices are synchronized to pass symmetry from the core. Core
positivity passes by arbitrarily small rational errors. Existential norm
ceilings are used only inside proofs of propositional form laws; the public
cutoff function takes the ceilings as data. Positivity and symmetry then
descend to the quotient domain by quotient induction.

## Declaration evidence

All paths in this table start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Content |
| --- | --- | --- |
| `norm_le_dist_of_orthogonal`, `completedDist_sub_le` | `BF4WilsonAllNomeGraphDistance.lean:139`, `:149` | Orthogonal norm comparison and explicit subtraction error budget |
| `logPartial_time_nonnegative`, `regularizedLog_time_nonnegative` | `BF4WilsonAllNomeLogRangePositive.lean:105`, `:113` | Positive original-time/core pairing |
| `GraphLimit`, `core` | `BF4WilsonAllNomeLogGraph.lean:76`, `:84` | Actual sequences/moduli and constant core witnesses |
| `graph_time_pin`, `graph_zero_input` | `BF4WilsonAllNomeLogGraph.lean:95`, `:112` | Commutation at the limit and closability |
| `subtract`, `graph_single_valued` | `BF4WilsonAllNomeLogGraph.lean:126`, `:145` | Synchronized quarter modulus and uniqueness |
| `core_nonnegative`, `core_symmetric` | `BF4WilsonAllNomeLogGraph.lean:161`, `:165` | Form laws for the actual core pairs |
| `diagonal` | `BF4WilsonAllNomeLogGraph.lean:171` | Explicit flattening of witnessed graph limits |
| `Domain`, `input`, `action`, `input_injective` | `BF4WilsonAllNomeLogGraph.lean:208`, `:211`, `:216`, `:221` | Quotient domain embedded in the unchanged carrier |
| `fromTime`, `input_fromTime`, `action_fromTime` | `BF4WilsonAllNomeLogGraph.lean:229`, `:232`, `:234` | Every actual positive-time image is a domain input |
| `vacuum_input`, `vacuum_action` | `BF4WilsonAllNomeLogGraph.lean:237`, `:240` | Original vacuum pin and zero action |
| `scale`, `add` | `BF4WilsonAllNomeLogGraphLinear.lean:96`, `:118` | Actual graph-witness closure with explicit moduli |
| `domainAdd`, `domainSmul` | `BF4WilsonAllNomeLogGraphLinear.lean:132`, `:143` | Rational operations on the existing quotient domain |
| `input_add`, `action_add`, `input_smul`, `action_smul` | `BF4WilsonAllNomeLogGraphLinear.lean:153`, `:160`, `:167`, `:174` | Exact input/action linearity |
| `graphPairingModulus`, `graph_pairing_close` | `BF4WilsonAllNomeLogGraphForm.lean:80`, `:90` | Computed all-tail pairing cutoff and its checked bound |
| `graph_nonnegative`, `graph_symmetric` | `BF4WilsonAllNomeLogGraphForm.lean:127`, `:142` | Form laws for every witnessed graph limit |
| `action_nonnegative`, `action_symmetric` | `BF4WilsonAllNomeLogGraphForm.lean:193`, `:200` | Positive symmetric action on the actual quotient domain |

## Main-frontier review: no response-to-signed-energy shortcut

The preceding `BF4WilsonAllNomeLocalConnectedFloor.faceExcitation_response_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeLocalConnectedFloor.lean:163`, bounds
ONE original plaquette's positive-time response on the reflected Wilson
completion. Its common spectator quadratic is not the conditional residual
Gram of an arbitrary state.

`BF4ExactSlabSignedNeighborEnergy.signedNeighborEnergy`,
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:50`, is an
ordered sum of distinct-neighbor residual pairings on `fullData` for an
arbitrary completed state. `conditionalGenerator_square` at `:68` retains
this signed sum, the diagonal conditional energy and positive remote terms.
These are conditional-link dynamics, not OS time. The response theorem
does not inhabit the signed-energy estimate's inputs.

The existing actual producer
`BF4ExactSlabConditionalGeneratorLowerBound.signedNeighborEnergy_lower`,
`lean/YMGap/Continuum/BF4ExactSlabConditionalGeneratorLowerBound.lean:71`,
still requires `heatRatio w<=1/2` and `heatRemainderBound w<1`.
`existingNome_generator_square_lower` at `:104` provides a positive pilot
coefficient, not a justified continuum scaling family. This increment
neither removes those guards nor supplies a useful replacement coefficient.

## Downstream interface review

There is no established SAME-carrier physical-Hamiltonian consumer filled
by this result. `GNSHamiltonian.SelfAdjointHamiltonianResidual`,
`lean/YMGap/Continuum/GNSHamiltonian.lean:285`, expects a total map on a
`CompleteGNSHilbert` carrier. `BoundedFunctionalCalculusResidual`,
`lean/YMGap/Continuum/SelfAdjointHamiltonian.lean:437`, expects a total
additive map on `GNSCompletionSpace D`. Neither is this reflected carrier's
partial graph. Their field names are not a proof of self-adjointness or
physical-time identification for the newly constructed action.

The existing `positiveTimeRangeApproximation`,
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeRange.lean:84`,
approximates supplied T-images by T^2-images, not arbitrary carrier states.
`completedTime_one_not_injective_width_one`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:94`,
exhibits the actual noninjectivity of T at width one. Do not replace either
statement with a full-carrier dense-domain or invertibility assertion.
The concrete consumer of the new distance/core-form lemmas is the actual
graph construction above; no larger J02 interface is marked inhabited.

## Remaining boundary and execution priority

Graph closedness here means closure under supplied graph witnesses and
supplied simultaneous moduli. It does not select witnesses for an arbitrary
sequence of quotient-domain elements. Full-carrier dense domain,
self-adjointness, a scalar-log identity, a continuous-time semigroup and a
physical Hamiltonian are NOT proved. The known boundary kernel is not
discarded or identified with zero in the carrier.

The useful signed original-action spatial/scaling estimate remains the
primary producer. Same-object thermodynamic/scaling comparisons, nontrivial
continuum survival, finite physical-mass calibration, full QFT axioms and
every-group construction also remain open. This independent operator-domain
work is not a replacement for them. Do not continue adding generic graph or
scalar-calculus wrappers in place of producing the missing analytic bound.
No canonical chart node changes.

## Verification

Five final focused serialized checks passed all 43 printed gates, within
{propext, Quot.sound}. GraphDistance has 3, LogRangePositive 2, LogGraph 21,
LogGraphLinear 9 and LogGraphForm 8. The graph-pairing cap definition is
axiom-free; its nonnegativity uses only propext. The other printed gates
report propext and Quot.sound. Initial namespace/binder elaboration errors
were corrected before the successful final checks. No sorry, custom axiom,
classical choice or new analytic hypothesis was introduced.

Logs under `/tmp/`: `ym-log-graph-distance-20260930.log`,
`ym-log-range-positive-20260930.log`, `ym-log-graph-20260930.log`,
`ym-log-graph-linear-20260930.log`, `ym-log-graph-form-20260930.log`.
No full-root build, global axiom audit or frontier guard was run. Root
imports are registered without claiming a root compilation.

Luna proved the distance helpers and traced downstream carrier boundaries.
Sol proved core positivity, domain linearity and graph form laws; root
constructed the closable graph/domain and explicit diagonal, reviewed the
moduli and performed all serialized checks. Independent source review
kept the primary signed/scaling obligation distinct from this increment.
The safe-build skill kept one worker, a 20 GiB worker ceiling, a 12 GiB OS
reserve and continuous safety telemetry. Every final check completed in
its initial tool call, so no live long-job polling was needed. Routine
literature scanning was not repeated inside the 12-hour cache interval.
