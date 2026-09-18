# Same-carrier one-step Wilson positivity

Date: 2026-09-18 UTC. Starting commit: `540645d`.
All seven new focused Lean targets passed. The actual original one-step
quadratic is now proved nonnegative on EVERY vector of the current real
Wilson spatial-union completion. On its current direct complexification,
the full quadratic is real and nonnegative. This is a same-carrier join,
not a strict bound, spectral theorem or continuum construction.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory full QFT axioms, an
isolated vacuum and a finite positive physical Hamiltonian mass gap.
**OPEN.**

## The mathematical join

Write ell(h)=H[V*h] and W_R(f,p) for the original half-open observed-window
message. Reversing every slice of the complete chain gives the identity

    ell(W_R(f,p)*g) = ell(f*W_R(g,reverse_R(p))).

The kernel is compared using its actual two-slice swap symmetry. Every V,
including the endpoint weights, occurs exactly once. The supported probe p
may be an arbitrary signed multi-time polynomial; it is not required to
factor into one-slice probes. All coordinate support is checked before
removing common padding.

For F=W_R(u_t,p), the separated-window numerator with a single central
transition is therefore

    inputNumerator(R,t,T F,reverse_R(p)) = ell(F*T F) >= 0.

The final inequality is the previously checked original interacting
quadratic, not a new positivity hypothesis. Its identity T f=P(V*f) keeps
the full spatial action V inside both kinetic Gram arguments:
`original_quadratic_pin` and `transferStep_quadratic_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:56`
and `:67`.

The denominator remains the original total-chain partition with
2*t+2*R+1 transitions. Its constructed positive certificate retains
0<w<1 and headCutoff(w)<=K. No positive-F premise, replacement action,
independent normalization or finite stationarity is used.
The existing separated identity is `windowRatio_separated_joint`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedWindowPins.lean:112`;
partition positivity is `inputPartition_terminal_positive`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowTwoBoundary.lean:61`.

## The extra slice is removed only in the limit

For an intrinsic expression of radius R, the one-step pair has lower
offsets j and upper offsets 2*R+1-j. This fits an odd window of length
2*R+1. The actual intrinsic common chart uses horizon R+1 and displayed
length 2*R+2. A finite symmetric boundary pair (t,t) on that larger chart
trims to (t,t+1), not (t,t).

The proof first establishes positivity on the balanced odd window. It
then uses `originalJoint_padding` with (left,right)=(0,1),
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonLimitStationarity.lean:96`.
Thus the existing time/cutoff limits agree before the spatial regulator
recedes. No new odd-window spatial state or modulus is chosen.
`jointLimits_spatial_converge`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:85`,
retains the existing spatial construction and its small-nome guards.

The final completion step uses the existing mixed-pairing convergence for
each supplied Cauchy stream, including streams with growing spatial bases
and time radii: `pairSequence_converges`,
`lean/YMGap/Continuum/CRealSeminormPairingCompletionLimit.lean:95`.
Quotient induction does not select representatives by choice. On the
current direct complexification, the real part is the sum of the two real
quadratics and the imaginary part vanishes by time balance and symmetry.

## Verification boundary and remaining work

The parent ran seven final focused checks through the monitored launcher,
serialized with one worker and an explicit 20 GiB limit. All 31 public
gates and seven internal diagnostic gates lie within {propext, Quot.sound};
`reverse_within` is axiom-free. The parent inspected the full sources and
the revised proof sections; independent reviews checked the finite
numerator, all supports, original partition, boundary correction and
current completion transport.

The initial reversal drafts required local elaboration fixes. A subsequent
successful compilation was REJECTED by the axiom gate: this toolchain's
core `List.nodup_range` depends on `Classical.choice`. The final proof uses
the existing constructive `range_nodup`,
`lean/YMGap/Continuum/CayleyParentInj.lean:124`. Direct helper diagnostics
identified this exact dependency; the final reversal gates and all
downstream gates are clean. The finite consumer required an explicit
unfolding of weightedMass; the intrinsic consumer required a qualified
proof constructor. No mathematical statement or analytic guard changed.

Seven semantic-root imports were added. Full-root/full-tree build, audit,
guard and progress runs were NOT performed. No sorry introduced or
discharged, custom axiom, retained classical dependency or new analytic
certificate. Canonical frontier statements, guards, CI settings, resource
policy and whole-project goal are unchanged. No canonical atom closes.

## Declaration map

| Result | Declaration and source |
| --- | --- |
| Explicit chronological block reversal | `sliceReverse`, `lean/YMGap/Continuum/SU2QuaternionSliceReversal.lean:41` |
| Whole supported subwindow recoding | `reversePolynomial_lift`, `lean/YMGap/Continuum/SU2QuaternionSliceReversal.lean:197` |
| Original closed action reversal | `closedChain_reversal`, `lean/YMGap/Continuum/SU2QuaternionHeadWindowReversal.lean:366` |
| Signed whole-window adjointness | `windowMessage_reversal`, `lean/YMGap/Continuum/SU2QuaternionHeadWindowReversal.lean:415` |
| Actual one-step source geometry | `oneStep_chart_source`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOddWindow.lean:122` |
| Odd-window joint limits give the current intrinsic form | `oddJointLimits_oneStep_converge`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOddWindow.lean:156` |
| Original ordered Wilson source reversal | `source_reverse`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSourceReversal.lean:66` |
| SAME interacting quadratic numerator | `reversed_input_quadratic_pin`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOddWindowPositive.lean:55` |
| Positive original normalized odd window | `reversed_windowRatio_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOddWindowPositive.lean:81` |
| Actual original finiteValue positivity | `originalOddScalar_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonTimePositive.lean:91` |
| Intrinsic one-step positivity after the existing limits | `intrinsicForm_oneStep_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonTimePositive.lean:114` |
| Every current real completion vector | `completedInner_oneStep_nonnegative`, `lean/YMGap/Continuum/BF4WilsonSpatialUnionTimePositive.lean:80` |
| Full complex quadratic real and nonnegative | `inner_oneStep_nonnegative`, `lean/YMGap/Continuum/BF4WilsonSpatialUnionTimePositive.lean:88` |

## Next backward input, not an assumed certificate

For a same-operator continuous-time construction, positivity alone does
not eliminate kernel vectors. A sufficient next analytic input is a
computed residual-decay modulus on every current dense Wilson stage for
the powers of I-T^2. A finite geometric sum would then be an approximate
preimage, not an exact or bounded inverse.

The existing proof of that finite-sum identity is
`partialPreimage_identity`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeApproximation.lean:60`.
Its `rangeApproximationData` and `zeroContinuityData` consumers are in
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicFullSpaceZeroContinuity.lean:86`
and `lean/YMGap/Continuum/BF4ExactSlabThermodynamicFullSpaceZeroContinuity.lean:112`.
These are LEGACY plaquette-carrier results, not current Wilson instances.
The legacy sufficient dual estimate is `completed_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTransferTestBound.lean:132`,
consumed by `dense_residual_small`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDenseResidualDecay.lean:81`.
Do not import their conclusions as if their carriers agreed. Current
represented row limits already commute with the actual time maps:
`rowLimit_time`, `lean/YMGap/Continuum/BF4WilsonSpatialUnionCauchyRows.lean:63`.
The new positivity theorem supplies no residual-decay modulus or current
dense-range instance. The primary scale-controlled interacting estimate
remains a separate, higher-priority analytic task.

This is one-step quadratic positivity on the existing fixed-spacing,
small-nome SU(2) carrier. It is not a new strict estimate or a spectral
theorem. The primary regulator-controlled generated-Wilson-orbit bound,
changing-spacing family and nontrivial continuum survival, physical-time
generator/mass calibration, full same-theory continuum QFT construction,
and every compact simple group remain open. Positivity alone does not
establish injectivity, a logarithmic generator or a physical mass gap.

## Verification artifacts

Source filenames in this table are under `lean/YMGap/Continuum/`.

| Artifact | SHA256 |
| --- | --- |
| `/tmp/ym-slice-reversal-retry1-20260917.log` | `2ed7b6be17a82d537c10754813f1953c21733dfa94fa0f2d51e4d895f93aadbf` |
| `/tmp/ym-wilson-odd-window-20260917.log` | `7d4c7cfae9fb29f70d42e287b9dcf848d0caba99f5a79d2c0204864794795b76` |
| `/tmp/ym-head-window-reversal-constructive-20260918.log` | `620cc7bdf25f8b2133fc5457524345e0fe45ee85eac105590e64cc12ff9b333a` |
| `/tmp/ym-wilson-source-reversal-20260918.log` | `710ed24e74975e02b642cbbf9d2f655181ee7e967c524208bfad1f5c85565dec` |
| `/tmp/ym-odd-window-positive-retry1-20260918.log` | `d7b53e02724f27cf3b35136761d17ce72bdb17b551c108d15e9e2c3fe011c51b` |
| `/tmp/ym-wilson-time-positive-retry1-20260918.log` | `1c0472f142542e7d9ab929a0a991d0aafe548e2e7f49d6ca6e441e676c48fac8` |
| `/tmp/ym-wilson-completed-time-positive-20260918.log` | `53a13347fb5650278bbd3c6f4172386b033d1564e13dfbc1d89951f502b4f6a2` |
| `SU2QuaternionSliceReversal.lean` | `63f9d059cad04dbd902c7ceaf26b77036c235ab0e90db1e17378a6aef8bcf8b4` |
| `SU2QuaternionHeadWindowReversal.lean` | `5a01de55bed14a635ee78043b3ab1b291a32762cfc7a75230c87fdcbec3e35d8` |
| `BF4ExactSlabFixedSpatialWilsonOddWindow.lean` | `feac15397f95d1a15d84168740c8616e9eb590f9980277be70b1d29dfbd20a9a` |
| `BF4ExactSlabFixedSpatialWilsonSourceReversal.lean` | `9a49e97cf497cb3d734898bddbdf94452b2739afa6224e9827c0a37e44286682` |
| `BF4ExactSlabFixedSpatialOddWindowPositive.lean` | `5b0153bdd62d9646eccbadba8141e14f4927a42e7a5f75d0b213c51b0e8d8beb` |
| `BF4ExactSlabFixedSpatialWilsonTimePositive.lean` | `682c8d8677aa2257429b9a6f3de710a653431113a1a2072ec4307b8984e9f142` |
| `BF4WilsonSpatialUnionTimePositive.lean` | `52c032825dbd30cc618eda07e728cfc0302cd5797cd091b787451d32d972047d` |
