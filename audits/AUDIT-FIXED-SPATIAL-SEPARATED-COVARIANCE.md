# Original separated-window connected covariance

Date: 2026-09-16. Classification: PROGRESS after `be767d0`.

WHOLE-PROJECT GOAL: nontrivial continuum Yang--Mills on R^4, required QFT
axioms and positive physical Hamiltonian gap for every compact simple
group, on the SAME theory, within the constructive axiom gate. This finite
SU(2) result does not close the continuum or Clay target.

## Mathematical result

For supported signed polynomials P on L+1 slices and Q on R+1 slices, let
Q be placed at offset L+g in the total window S=L+g+R. With the SAME
original action and partition for all three expectations,

    |E(P * shifted Q) - E(P) * E(shifted Q)|
      <= (capQ+capQ) * (q^g * (capP+capP)).

The rate q=mixRate belongs to [0,1), depends on nome w and spatial width,
and is independent of late heat cutoff K>=headCutoff(w). The bound is
independent of the two external boundary lengths. Probe caps remain explicit;
changing probes with a parameter requires controlling their caps separately.
The separation g counts transitions from the final slice of P's window to
the first slice of Q's window, not strictly intervening slices.

Expansion exposes the original window messages, the common positive
partition and the two certified residuals. Contraction then composes:

1. Exact polynomial factorization gives F=T^g(windowMessage(L,u_m,P)).
   The right window is tested against F, while its unobserved comparison
   input is U=u_(m+L+g). All original kinetic/spatial factors remain.
2. The existing actual bracket gives certificates F-l*U and b*U-F,
   with b-l=2*capP*q^g. Its endpoints need not be positive.
3. Write J for the right observed numerator, Z for its unobserved mass,
   and D=F-l*U. Positivity and signed insertion control give
   0<=Z(D)<=(b-l)*Z(U), |J(D)|<=capQ*Z(D), and
   |J(U)|<=capQ*Z(U). The cancellation
   J(F)*Z(U)-Z(F)*J(U)=J(D)*Z(U)-Z(D)*J(U)
   precedes absolute values. Hence the numerator is bounded by
   2*capQ*(b-l)*Z(U)^2.
4. The actual unobserved partition is proved positive. Its reciprocal
   cancels Z(U)^2 exactly, with no reciprocal ceiling. Neither an observed
   message mass nor a residual mass is inverted. Joint and both marginals
   are pinned to the same m,S,n window before applying this normalization.

## Declaration evidence

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `step_mul_lift`, `iterateStep_mul_lift`, `iterateStep_middle` | `SU2QuaternionHeadSeparatedWindows.lean:55`, `:69`, `:94` | Explicitly lifted future factors survive the integrated heads. |
| `windowMessage_separated` | `SU2QuaternionHeadSeparatedWindows.lean:108` | Exact two-window chronological factorization. |
| `inputCovariance_bracket_bound` | `BF4ExactSlabFixedSpatialInputCovariance.lean:121` | Signed determinant bound with common partition square; zero mass allowed. |
| `covariance_bound` | `RationalCommonPartitionCovariance.lean:23` | One positive partition normalizes joint and both marginals. |
| `separatedMessage`, `separatedMessage_one` | `BF4ExactSlabFixedSpatialSeparatedWindowPins.lean:53`, `:69` | Actual propagated insertion and unit-message pin. |
| `separatedPartition_eq` | `BF4ExactSlabFixedSpatialSeparatedWindowPins.lean:82` | Literal equality of the two unobserved partition presentations. |
| `windowRatio_separated_joint`, `windowRatio_separated_left`, `windowRatio_separated_right` | `BF4ExactSlabFixedSpatialSeparatedWindowPins.lean:112`, `:133`, `:164` | Identical total-chain scalar pins. |
| `separated_input_bound` | `BF4ExactSlabFixedSpatialSeparatedCovariance.lean:54` | Actual shrinking bracket supplies the normalized bound. |
| `windowRatio_covariance_bound` | `BF4ExactSlabFixedSpatialSeparatedCovariance.lean:95` | Connected expectation bound with identical m,S,n. |
| `polynomialWindow_covariance_bound` | `BF4ExactSlabFixedSpatialSeparatedCovariance.lean:117` | Constructed intervals and polynomial caps; no assumed covariance estimate. |

Rate evidence: `BF4ExactSlabFixedSpatialTransferMixingRate.lean:110`,
`mixRate`; `:113`, `mixRate_nonnegative`; `:124`, `mixRate_lt_one`.
Bracket width: `BF4ExactSlabFixedSpatialWindowBracket.lean:88`,
`windowBracket_width`. Signed residual control:
`BF4ExactSlabFixedSpatialWindowInput.lean:201`, `inputNumerator_abs_le`.

## Boundary review

- Zero gap uses q^0; neither g nor q is inverted. q=0 is permitted.
- Zero block count and zero window lengths require no special positivity
  premise. Generic algebra has no support hypotheses; support enters when
  the fully contracted left message is propagated in the certified cone.
- A zero reference partition is permitted by the unnormalized estimate;
  the final original-action specialization constructs its positive partition.
- Signed endpoints and zero residual mass cause no division failure.
- The final spatial V remains exactly once in weightedMass.
- Lifted units have padded zero exponents: the left pin uses exact iterate
  composition, not a false raw coefficient equality for lifted polyOne.

Independent source review found no defect in these boundaries. Kernel
verification is recorded separately below. No new analytical hypothesis,
sorry, axiom, canonical frontier field, resource limit or CI setting changed.

## Next consumers: reviewed plan, not proved here

The reflected placement and connected-limit estimate are still open.
The source-reviewed index choice is R=max(radius x,radius y), H=R+n;
use left length R, gap n, right length H, total 2H. The lower observable
is sourceSpan(encodeChart R y); the upper is sourceSpan(x) lifted by H*N.
The latter polynomial stays fixed while its support bound is enlarged.

`BF4ExactSlabFixedSpatialPhysicalTimeShift.lean:147`, `encodeChart_advance`,
already handles the lower offsets. The guarded mirror/encode identity and
arbitrary-advance PADDED source-span pin still need proofs. The one-step
template is `BF4ExactSlabFixedSpatialCenteredWindowShift.lean:135`,
`sourceSpan_shift`; finite padded transport is
`BF4ExactSlabFixedSpatialWindowPaddedCongruence.lean:82`,
`windowRatio_padded_congr`. Use the inequality `radius_advance_le` at
`BF4ExactSlabFixedSpatialPhysicalTimeShift.lean:125`, not radius equality
for empty schedules.

After those pins, the existing consumers are
`BF4ExactSlabFixedSpatialCommonChartCorrelator.lean:72`, `chartScalar_pin`,
and `BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.lean:91`,
`connectedScalar_converges`, with the SAME completed physical-time identity
`centeredTime_originalCorrelator` at `:126`. No new stationary law or
interchange of cutoff/time limits is justified by this finite theorem.

For later prefactor removal, the model-independent scalar engine is
`Z4HalfTimeReflectionStrictJointDenseDyadicGap.lean:365`,
`dyadic_geometric_first_le`. It requires positive rational rate/prefactor,
nonnegative anchored moments, dyadic CS and the geometric envelope. A
source-reviewed candidate is the explicit centered covariance representative
at lag 2*k, rate q*q and enlarged positive prefactor. Existing completed CS
(`BF4ExactSlabFixedSpatialCompletedGeometry.lean:46`,
`completedInner_cauchySchwarz`), time balance
(`BF4ExactSlabFixedSpatialCompletedTimeForm.lean:58`,
`completedInner_time_sum`) and centered even-time bounds
(`BF4ExactSlabFixedSpatialCenteredPhysicalTime.lean:122`,
`centered_even_nonnegative`, and `:127`, `centered_even_le_identity`) are
the intended inputs. q=0 needs a direct envelope branch. This application
and its completed-complement extension are NOT checked here; no old-model
specialization is silently applied to the actual new objects.

Strict reflected-norm contraction, nonconstant excitations, vacuum isolation,
metric completeness, full Hilbert/OS/gauge-algebra reconstruction, joint
cutoff/time limits, spatial/spacing control, physical mass calibration,
continuum QFT and all-group Clay closure remain open.

## Focused verification

Five focused checks passed, serialized with one worker and a 20 GiB hard
ceiling, each preceded by a fresh process/swap check. All 15 public axiom
gates report only {propext, Quot.sound}. Final logs have no errors, warnings,
sorryAx or classical dependencies. A zero-product simplification and typed
scalar transport repaired initial elaboration failures without changing
statements or resource limits. In particular dependent partition rewriting
was replaced by a small generic reciprocal-congruence proof.

Five imports were added to the selective root; no root/full-tree/full axiom
audit was run. Main alone compiled. CI remains unchanged. No literature
scan was performed; the existing twelve-hour policy remains in force.

| Module | Gates | Final `/tmp/<module>.log` SHA-256 |
|---|---:|---|
| `SU2QuaternionHeadSeparatedWindows` | 4 | `0dd6c4ace61341c6aaf83f92dc414f5ebd7f9175e356bf7655fc8ccb9f541b91` |
| `RationalCommonPartitionCovariance` | 1 | `e4db3c55e67313e0346e82a731785476e89897448507a7538aa460b553be9de3` |
| `BF4ExactSlabFixedSpatialInputCovariance` | 1 | `8460cc7b9e070b4b9ba0f967d644b321713e2dcb0c68460fc453bc44156777d8` |
| `BF4ExactSlabFixedSpatialSeparatedWindowPins` | 6 | `be9b6bc6fae72d3eb6d224356044a60c04b81e514220909d01132a261bb7d0ad` |
| `BF4ExactSlabFixedSpatialSeparatedCovariance` | 3 | `bbde2e2b66e30437ba3ddac68dc18aa901f1af0eedb058e1991bef32585c5345` |
