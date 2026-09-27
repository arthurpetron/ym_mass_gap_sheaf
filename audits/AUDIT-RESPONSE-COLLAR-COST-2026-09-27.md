# Response collar-cost obstruction and the next analytic estimate

Date: 2026-09-27. Base: `58bf268`.

The new result rules out one proposed scalar termwise estimate. It does not
prove spatial decay, close a canonical frontier atom, or refute Yang--Mills.

## Checked calculation

Write h = headFloor(w), c = collarCount(roots, anchor). The existing floor
and cost are h^(4c+2) and its positive reciprocal. The literal incidence
budget is c = 6*(roots.length + 4*anchor.length). Adding one anchor increases
c by 24; the next floor is therefore the old floor times h^96.

For any rational activity a, a nonincreasing scalar step

    a * collarCost(w, c+24) <= collarCost(w, c)

forces a <= h^96. The existing bound 0 < h <= 1/32 implies that this is
impossible for a = w^3 whenever 1/32 <= w < 1. The proof compares only
(1/32)^3 and (1/32)^4; it does not expand a 96th power numerically.

| Declaration | Source | Checked statement |
|---|---|---|
| `collarFloor_power` | `lean/YMGap/Continuum/BF4ExactSlabResponseCollarCostObstruction.lean:39` | Original floor equals h^(4c+2). |
| `collarCount_cons` | same module `:52` | Appending a core entry costs 24 in the literal incidence budget. |
| `collarFloor_step` | same module `:59` | Next floor equals old floor times h^96. |
| `oldCost_nextFloor` | same module `:71` | Exact reciprocal cancellation leaves h^96. |
| `activity_le_floor_of_nonincrease` | same module `:85` | Nonincrease requires a <= h^96. |
| `no_cubic_cost_nonincrease` | same module `:107` | The cubic proposal fails for w >= 1/32. |
| `no_cubic_anchor_cost_nonincrease` | same module `:124` | Same result for the actual root/core incidence formula. |

The floor ceiling used here is
`BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`.

## Exact scope and causal consequence

`rooted_response_term_bound`,
`lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:94`,
multiplies the absolute coefficient by this cost. The new theorem prevents
using a cubic-per-added-core-face scalar gain to make that cost contract
in the displayed nome range. It supplies no lower bound on the actual
coefficient: the coefficient could be much smaller, including zero.
It proves neither divergence of the signed sum nor impossibility of
clustering. No assertion about sharpness of the incidence budget is made.

In particular, `response_distance_activity`,
`lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:127`,
extracts ONE global w^3, not a w^3 for every core face. No additional
per-face estimate is silently attributed to it.

The next analytic attempt must account for the loss before taking absolute
values: estimate the actual normalized signed `distanceActivity`
(`lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:117`), or
improve the partition comparison enough to support a genuinely summable
coefficient estimate. Its current consumer is
`covariance_response_bound_of_rooted`,
`lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:118`.
The quantitative hypothesis in that consumer is still unsupplied.

Source review also found that one-face variance-relative response and
guarded volume-free coupling paths are already implemented:
`BF4ExactSlabCouplingScoreBound.face_response_variance_bound`
(`lean/YMGap/Continuum/BF4ExactSlabCouplingScoreBound.lean:273`) and
`BF4ExactSlabSummedCouplingPath.full_slab_original_change_bound`
(`lean/YMGap/Continuum/BF4ExactSlabSummedCouplingPath.lean:172`).
Repeating those would not remove the spatial small-nome guard.

## Targeted literature check, not a listing refresh

A primary-source search did not provide a replacement estimate. The abstract
of Shen--Zhu--Zhu's [stochastic lattice Yang--Mills paper](https://arxiv.org/abs/2204.12737)
states an explicit strong-coupling restriction. Adhikari--Cao's
[weak-coupling correlation-decay paper](https://arxiv.org/abs/2202.10375)
treats finite gauge groups. These abstract-level checks are not proof audits;
neither result is imported as an estimate for this SU(2) heat action or its
changing-spacing limit. The cached math-ph listing was reused, not refreshed.

## Verification boundary

The focused monitored check of the new module passed with one worker and
the mandatory 20 GiB ceiling. All seven printed declarations have axiom sets
{propext, Quot.sound}; no sorryAx or classical dependency. The initial check
exposed an indentation error and missing namespace opening, corrected without
changing any statement or raising limits. Sol independently reviewed the
calculation and scope. No full-tree build/audit, canonical field change, or
change to broad chart markers. Physical scaling, continuum QFT, and the
all-group Clay target remain open.
