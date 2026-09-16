# Actual SU(2) heat windows with an explicit AF budget

Date: 2026-09-15. Follow-up after `b3e252a`. These are checked estimates
on the ORIGINAL SU(2) character series and its finite Euler products,
not a construction of continuum Yang--Mills or a physical transfer gap.

## 1. Mathematical reduction

For rational 0<w<1, set N=HeatRoundedCutoff.cutoff(w). The previous
checkpoint gives w^N<=1/8 and N*(1-w)<=9. The new argument is finite:

1. q-Pascal bounds each Gaussian-binomial coefficient by 2^degree.
   Its exact Euler normalization compares the first N factors to the
   next N, giving E_w(N)>=(1/8)^N.
2. Group the remaining factors into blocks of N. Their product dominates
   E_(w^N)(B)^N. Since w^N<=1/8, a geometric-loss estimate gives
   E_(w^N)(B)>=1/2 for every finite B. Hence E_w(K)>=(1/16)^N
   for EVERY finite K. No infinite-product denominator is assumed.
3. The existing window lower endpoint is its retained Euler prefix squared
   divided by 64. Consequently 1<=4^(4N+3)*lower(w).
4. The ORIGINAL squared-dimension/Casimir majorant is <=4^n always and
   <=(1/2)^n when n>=N. This bounds every majorant prefix and even the
   old representation-dependent tail overestimate: prefixCap(w)<=4^(N+1).
5. The existing finite-prefix positivity and tail modulus construct
   positive windows with lower=F(w)/4 and upper=prefixCap(w)+lower.
   Their actual spread is <=4^(5N+5). Choose bits(w)=5N+5.
6. Since N>=1, bits<=10N. The AF margin and the previous N*t/4<=18
   therefore give bits*t/4<=180. Windows, spread and growth use exactly
   this same actual-nome schedule.

The larger bit schedule is sufficient for the UNCHANGED generic interface.
The sharper spread cap 4^N has not been proved or assumed. No old field
or theorem statement was weakened to obtain this construction.

## 2. Declaration-level evidence

All shortened file names in the table are under `lean/YMGap/Continuum/`.

| Result | Declaration and source |
| --- | --- |
| Gaussian-binomial cap | `qbin_nonnegative`, `EulerRoundedHeadFloor.lean:33`; `qbin_le_two_pow`, same file `:64` |
| Original Euler head | `head_floor`, `EulerRoundedHeadFloor.lean:130` |
| Blocked small-nome product floor | `small_nome_floor`, `EulerRoundedBlockFloor.lean:40`; `segment_constant_floor`, same file `:69`; `block_comparison`, same file `:87` |
| All-length Euler bound | `euler_floor`, `EulerRoundedBlockFloor.lean:129`; `rounded_euler_floor`, same file `:153` |
| Actual window data | `lower`, `SU2PointwiseHeatPositiveWindow.lean:35`; `depth`, same file `:38`; `upper`, same file `:43` |
| Positive original windows, including endpoints | `window`, `SU2PointwiseHeatPositiveWindow.lean:106`; `window_depth`, same file `:115`; uses `finiteFloor_le_prefix`, same file `:61`, and `tail_le_lower`, same file `:55` |
| Exact floor pin and exponential payment | `lower_formula`, `SU2RoundedHeatLower.lean:32`; `lower_paid`, same file `:69` |
| Actual Casimir suppresses the squared dimension | `majorant_le_half_pow_of_cutoff_le`, `SU2RoundedHeatUpper.lean:106`; `majorant_prefix_le_rounded`, same file `:155` |
| Existing full-prefix cap, including its old raw-cutoff tail | `closedTail_zero_le_rounded`, `SU2RoundedHeatUpper.lean:202`; `prefixCap_le_rounded_pow`, same file `:219` |
| Actual schedule and spread | `bits`, `BF4RoundedPositiveAFWindows.lean:36`; `window_spread`, same file `:45` |
| Heat cost and existing growth witness | `bit_heat_cost`, `BF4RoundedPositiveAFWindows.lean:85`; `growth`, same file `:107` |
| Existing generic window family, with no window/spread/growth premise | `windowFamily`, `BF4RoundedPositiveAFWindows.lean:119` |
| Literal blocked-nome specialization | `matchedWindowFamily`, `BF4RoundedPositiveAFWindows.lean:139` |
| Actual completed 23-factor product comparison | `retainedHarnack`, `BF4RoundedPositiveAFWindows.lean:155` |

Every finite-window depth is data depending on w, not an index extracted
from a propositional existence. The depth is common to all rational class
coordinates -1<=x<=1. It is independent of the Harnack bit schedule;
these are different roles in the existing type, not a silent cutoff swap.
The old prefix/floor values may depend on rational presentation, but their
new bounds use the proved representation-invariant N(w).

## 3. Actual consumer versus scalar arithmetic

`retainedHarnack` directly consumes the new windows/spread through
`dynamicPointwiseRetainedHarnack`,
`lean/YMGap/Continuum/SU2PointwiseHeatDynamicWindow.lean:499`.
Its target is the existing `DynamicCompletedRetainedHarnackData`,
`lean/YMGap/Continuum/BF4FarautJointCarrierAFBudget.lean:252`, for products
of 23 completed actual character kernels at supplied class coordinates.
It is not an identification of those coordinates or that product with the
original interacting transfer. The existing
`wholeSlabDynamicPointwiseConditionalPushforward_domination`,
`lean/YMGap/Continuum/SU2PointwiseHeatDynamicWindow.lean:635`, is a further
conditional consumer requiring its common nonnegative potential.

In contrast, `pointwise_af_window_family_perron_strict`,
`lean/YMGap/Continuum/SU2PointwiseHeatDynamicWindow.lean:961`, reads only
the family's bits in its proof. It still assumes qS<=1/4 and sufficient
depth. `NonlinearSpectralCertificate`,
`lean/YMGap/Continuum/FiveHolonomyPerronCutoff.lean:357`, likewise does
not pin its rational qS to an operator. No instance of an original physical
spectral ratio is supplied by choosing an arbitrary scalar qS.

## 4. Remaining obligations

The next analytic/identification step must retain the ORIGINAL action,
carrier, centered observables, normalization and operator: identify the
retained product/pushforward and prove a centered contraction rate for
that same operator. The local heat-window theorem does not discharge it.

`matchedWindowFamily` still takes `CubicMarginLaw` and
`PhysicalSpacingEnvelope`, defined at
`lean/YMGap/Continuum/BF4MatchedPhysicalAFBridge.lean:175` and `:333`.
No physical instance of either is constructed here. The separate
fine/coarse sign-and-spacing calibration issue remains as recorded in
`AUDIT-AF-DYADIC-BRIDGE.md`. The refuted exact dyadic bridge is not used,
and its original type remains preserved.

Changing-action spatial cancellation, original OS/physical-time transport,
continuum QFT/nontriviality and every compact simple group remain open.
This is an SU(2) local heat estimate with explicit nome dependence, not
a beta-uniform interacting mass-gap theorem.

## 5. Verification boundary

Six new proof modules, 37 public gates: four definitions use no axioms;
every other gate is within {propext, Quot.sound}. Eleven focused safe
launches, serialized with one worker and a 20 GiB ceiling. These include
four elaboration-correction reruns and one final added-consumer check.
No resource or heartbeat limit was raised; no dependency refresh was
needed. Final logs are clean and own/direct artifacts fresh. Six root
imports added; root/full-tree build/audit not run. CI remains manual-only.
No literal hole, custom axiom, canonical field or old statement changed.

Final log hashes:

- `/tmp/ym-euler-rounded-head-floor.log`:
  `6cf54459c004b29ecd5b0a9fce1a7404cc81e844008fbe071c4378822b2198f1`.
- `/tmp/ym-euler-rounded-block-floor.log`:
  `c8e303bd48f4c7c97590db82c7e8c51948e2eddabc9a9b3343d07b838de28a2d`.
- `/tmp/ym-pointwise-heat-positive-window.log`:
  `9a816e4dab29ac19e8aa23084c1de7abc152e068cea254936975bd30d68c0dc8`.
- `/tmp/ym-rounded-heat-lower.log`:
  `abc8c2f942737395185421156927ba832944b92ef836b3eb73ca5bda9548e83f`.
- `/tmp/ym-rounded-heat-upper.log`:
  `42a0804dffdb009e03d7913eb48b732ee396d1b6f07ff94025e34b956be81fd1`.
- `/tmp/ym-rounded-positive-af-windows.log`:
  `46ec86c706cfd5247b9b8869458d91c246c6f863c6e3a4ac779d2c58510ce45e`.
