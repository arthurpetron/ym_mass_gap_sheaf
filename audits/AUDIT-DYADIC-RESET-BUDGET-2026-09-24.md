# Dyadic reset amplification versus the actual available loss budget

Date: 2026-09-24 UTC. Scope: one numerical obstruction and its literal
square-selection consumer. Whole-project constructive continuum Yang--Mills
and physical mass gap for every compact simple group remain OPEN.

## Proved comparison

For 0<w<1, set r=starRatio(w), p=(1-r)^k and F=1-p-4*p*p. The definitions
use the existing exact rational qpow and do not assert that a reset
decomposition exists. Bernoulli and the proved star-ratio ceiling give

    F <= 1-p <= k*r <= k*(1-w).

For k<=4*L and L=2^scale, the new theorem establishes

    F - 192*L^3*(1-w) <= 0.

The SAME completed-state theorem
`BF4WilsonAllNomeCenteredVector.centered_dyadic_loss_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:194`, bounds
2*(B(v,v)-B(v,T(L)v)) by 384*L^3*(1-w). Thus 192 is the correct coefficient
for the available response-loss budget. Even if the proposed reset lower
variance estimate were proved, this particular subtraction could not certify
positive response at any admissible nome/scale.

This is an upper bound on the proposed LOWER-CERTIFICATE NUMBER, not an
upper bound on the actual variance. The cubic number is an available UPPER
loss budget, not a lower bound on actual loss. No negative actual response,
failure of physical survival, or Yang--Mills counterexample is asserted.

## Source evidence

| Declaration | Source | Content |
|---|---|---|
| `R1CornerAtoms.oneSub_qpow_le` | `lean/YMGap/Continuum/R1CornerAtoms.lean:45` | Existing Bernoulli defect inequality on 0<=a<=1. |
| `BF4ExactSlabStarVarianceLossObstruction.starRatio_le_nome_defect` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceLossObstruction.lean:54` | Existing computed star ratio is no larger than 1-w. |
| `BF4DyadicResetBudgetObstruction.residualMass`, `.resetFloor` | `lean/YMGap/Continuum/BF4DyadicResetBudgetObstruction.lean:33`, `:38` | Explicit numbers; no asserted density decomposition or independence. |
| `BF4DyadicResetBudgetObstruction.resetFloor_le_count_mul_starRatio`, `.resetFloor_le_count_mul_nomeDefect` | `lean/YMGap/Continuum/BF4DyadicResetBudgetObstruction.lean:55`, `:76` | F<=k*r<=k*(1-w). |
| `BF4DyadicResetBudgetObstruction.resetFloor_cubic_budget_nonpositive` | `lean/YMGap/Continuum/BF4DyadicResetBudgetObstruction.lean:86` | General k<=4*side(scale) certificate obstruction, with coefficient 192. |
| `BF4DyadicResetBudgetObstruction.selectedSublist_resetFloor_cubic_budget_nonpositive` | `lean/YMGap/Continuum/BF4DyadicResetBudgetObstruction.lean:123` | Actual selected sublist supplies the length bound; no missing Nodup or injectivity theorem is assumed. |
| `BF4DyadicWilsonSquare.square_length`, `.paddedSquare_edges` | `lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:65`, `:84` | Existing exact perimeter and literal padded-word identity. |

## Repointed next analytic input

The proof of `QuaternionHaarWordDifference.word_scalar_square_bound`,
`lean/YMGap/Continuum/QuaternionHaarWordDifference.lean:269`, calls
`.finite_square_bound` (`:238`) after the exact ordered-word telescope.
This discards the signed cross terms and introduces squared perimeter.
The actual edge-density consumer is
`BF4ExactSlabFixedSpatialWilsonKineticIncrement.word_increment_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:176`.
The subsequent time-convexity bound is already linear in elapsed steps:
`BF4WilsonAllNomeTimeIncrement.timeIncrement_linear`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeIncrement.lean:100`.

The next useful result must improve the SAME signed relative loss or supply
a stronger direct response along a justified scaling family. The existing
positive fixed-nome variance floor does not do so. Constructing reset
densities alone is not the next action under the unchanged cubic budget.
This source review supplies no new relative estimate; all actual scaling,
continuum/QFT/YM/UV, physical-mass and all-group obligations remain open.

## Verification and chart delta

The final monitored check used one worker, a 2 GiB cap, default elaboration
limits and the unchanged 12 GiB reserve, and exited zero. Its local log is
`/tmp/ym-gap-dyadic-reset-budget-check-2.log`. Six printed gates lie within
{propext, Quot.sound}; the two numerical definitions have empty axiom sets.
The initial launch was refused at the memory reserve; no compiler was
started by that attempt. Memory was remeasured before resumption, with no
threshold change. Local logs are evidence paths, not tracked artifacts.

No new source hole, axiom, analytic premise, weakened field or reset-density
assumption. One selective semantic-root import; full-root/full-tree build,
axiom audit, guard and progress suites NOT run. Schema 1 snapshot 17 records
this route limitation. Goal-node status changes: NONE. The canonical chart
block, symbols, labels, layout and frontier marker are unchanged.
