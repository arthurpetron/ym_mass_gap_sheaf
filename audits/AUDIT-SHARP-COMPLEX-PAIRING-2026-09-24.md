# Sharp complex pairing on the SAME completion

2026-09-24 UTC. This checkpoint supplies a J02 prerequisite on the existing
fixed-nome, fixed-width reflected carrier. It does not close J02 or any
continuum/Clay goal node.

## Mathematical increment and actual consumer

For the existing complex pairing I and its existing carrier, the new result is

    |I(x,y)|^2 <= I(x,x).re * I(y,y).re.

The constant is ONE. The previous continuity estimate had TWO on its right
side. The new pairing-error theorem gives

    |I(x,test)-I(y,test)|^2 <= distSq(x,y) * I(test,test).re.

For supplied test representatives Y, the existing positive rational
testNormCap bounds that same test's squared norm. The new explicit tolerance
is epsilon/testNormCap; the original X.limitRate consumes it. This improves the
allowed squared-norm tolerance, without assuming the index function monotone.
The time consumer uses the existing X.mapTime and the SAME discrete transfer.

## Proof chain

| Declaration | Source | Role |
|---|---|---|
| `finiteComplex_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFiniteComplexRealification.lean:281` | Phase alignment on the direct sum of two actual rational reflected forms. |
| `formComplex_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz.lean:54` | Pass the inequality through the original time-window limits. |
| `pairingComplex_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz.lean:197` | Use one computed chart for all four spans; convert the quarter-turn pairing to the conventional imaginary-part square. |
| `jointPairingComplex_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.lean:41` | Remove the heat cutoff using the existing intrinsic-pairing limits. |
| `representativeInnerComplex_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.lean:69` | Pass through the existing supplied representative limits. |
| `inner_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.lean:98` | Descend to the existing complexification of JointCompletion. |
| `pairing_error_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexSharpContinuity.lean:43` | Constant-one estimate for the original complex pairing difference. |
| `pairingTolerance`, `pairingRate`, `pairing_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexSharpContinuity.lean:66` | Explicit tolerance and convergence-index data; no selected quotient representative. |
| `time_pairing_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexSharpContinuity.lean:100` | Actual discrete-time matrix-coefficient consumer. |

The phase-aligned finite vector is R(x,y)y + R(x,Jy)Jy, where J is the
quarter-turn. Its pairing with x is L=R(x,y)^2+R(x,Jy)^2 and its norm squared
is L*R(y,y). Real Cauchy--Schwarz gives L^2<=L*R(x,x)*R(y,y).
Only the rational L is case-split: if L<=0 positivity finishes the bound;
otherwise its positive rational factor is cancelled. No CReal zero decision,
classical choice or selected phase of a quotient scalar is used.

The existing `BF4ExactSlabFixedSpatialReflectedCauchySchwarz.lean` changes only
visibility of its finite pairing/form and elementary laws. Their definitions,
normalization, physical guards and proofs are unchanged. In particular the
finite pairing is still the original windowRatio at headCutoff(w)+stage.

## Verification boundary

All checks were narrow, serialized, with a 2 GiB worker ceiling. The accepted
logs below report only {propext, Quot.sound}; no error or warning remains in
these final logs. The first three checks were completed earlier in the same
worktree and preserved unchanged; the final three were completed in this goal
turn. Together they cover 22 printed gates, not a full-tree audit.

| Leaf | Accepted log | Gates |
|---|---|---:|
| Existing finite reflected API | `/tmp/ym-gap-reflected-cs-public-check-1.log` | 3 |
| Finite complex realification | `/tmp/ym-gap-finite-complex-cs-check-4.log` | 4 |
| Reflected complex limit | `/tmp/ym-gap-reflected-complex-cs-check-1.log` | 2 |
| Intrinsic complex form | `/tmp/ym-gap-intrinsic-complex-cs-check-4.log` | 4 |
| Joint completed complex form | `/tmp/ym-gap-joint-complex-cs-check-1.log` | 3 |
| Sharp complex continuity | `/tmp/ym-gap-joint-complex-sharp-continuity-check-1.log` | 6 |

An initial intrinsic draft lacked a namespace open; it was repaired. A later
run stopped at the 12 GiB host-memory reserve. After observed recovery, the
scaled-chart rewrite was made explicit and heavy form definitions were kept
opaque locally; checking resumed without raising limits or lowering reserves.
Earlier finite draft elaboration/memory failures are not accepted checks.
Independent source review found no additional carrier, normalization or
constructivity defect; that review is separate from compiler verification.

The final consumer is added to `lean/YMGap.lean` for semantic integration.
No full-root/full-tree build, axiom audit, frontier guard or progress script
was run. No new hole, axiom, analytic premise or canonical field was added.

## Remaining causal frontier

A03 remains the original-source complete signed energy versus SAME interacting
variance on ONE justified changing-scale family, or direct response control.
The positivity-only comparison was refuted at the preceding checkpoint.
EVERY-state spatial/spacing control, SAME physical continuum limits, full
Hilbert/OS/QFT/YM/UV structure, physical Hamiltonian/mass calibration and every
compact simple group remain open. J02 is not relabeled or promoted by this
partial prerequisite. The chart block is unchanged; no goal-node status change.
