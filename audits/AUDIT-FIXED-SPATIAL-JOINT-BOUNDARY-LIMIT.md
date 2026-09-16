# Original joint cutoff/time limit and both orders of limits

Date: 2026-09-16. Classification: PROGRESS after `4c8d734`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, for the SAME theory, within the constructive axiom
gate. The result here remains a one-sided fixed-spatial-width boundary scalar.

## Mathematical argument

Let R(k,n) be the EXISTING originalTimeScalar at cutoff stage k and chain
length n: its ambient extent is width+n, its lower probe is the same fixed
physical fs, and its upper probe is empty. The actual selected action,
whole-chain reciprocal partition and terminal spatial V are unchanged.

The checked time-Cauchy modulus A(epsilon) is independent of k. For each
fixed n, the existing original finiteCauchy supplies a cutoff modulus C_n.
For delta=epsilon/4 define explicit natural-number functions

    a = A(delta), b = C_a(delta), D = max(a,b).

Whenever n,m>=a and k,j>=b, compare

    R(k,n) -> R(k,a) -> R(j,a) -> R(j,m).

Each comparison costs delta, in both order directions. Adding one unused
quarter of nonnegative slack gives a rectangular epsilon bound. In the
middle comparison both time and extent/insertion are fixed at a. No cutoff
estimate uniform over all time lengths is assumed or needed.

The literal diagonal R(s,s) has QCauchy modulus D. Its constructed CReal
originalJointLimit controls the whole late rectangle, not merely this
diagonal. This is proved with the existing explicit QMhat reindex and
self_le_QMhat, not compactness or selection.

For cutoff-first passage, the existing original expectation at time n has
representative R(QMhat(row_n)(i),n). For time-first passage, the existing
boundaryTimeLimit at stage k has representative equal, through the already
proved originalTimeScalar_pin, to R(k,QMhat(time_k)(i)). Since QMhat(i)>=i,
the same rectangle bounds both against the common limit representative.
The two approximation indices are independent in the bound statements.
Both orders therefore converge to the SAME returned scalar; no second
completion or newly supplied limit object is used.

## Declaration evidence

Paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `originalCutoffCauchy` | `BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:35` | Existing finiteCauchy of the fixed-time original action. |
| `jointTimeThreshold`, `jointCutoffThreshold`, `jointModulus` | `BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:45`, `:51`, `:57` | Explicit a, b and max(a,b). |
| `originalJoint_rectangle` | `BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:89` | Paired estimate for two independent cutoff/time pairs. |
| `originalJointCauchy`, `originalJointLimit` | `BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:112`, `:123` | Diagonal Cauchy datum and returned CReal. |
| `originalJoint_diagonal_converges`, `originalJoint_approx` | `BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:128`, `:137` | Diagonal convergence and control of the full late rectangle. |
| `originalCutoffExpectation`, `originalCutoff_converges` | `BF4ExactSlabFixedSpatialOriginalJointLimits.lean:38`, `:47` | Literal existing original expectation, with its inner cutoff convergence. |
| `originalCutoffExpectation_approx_joint`, `originalCutoffExpectation_converges` | `BF4ExactSlabFixedSpatialOriginalJointLimits.lean:59`, `:79` | Cutoff-first, then time, with explicit representative bounds. |
| `boundaryTimeLimit_approx_joint`, `boundaryTimeLimit_converges_joint` | `BF4ExactSlabFixedSpatialOriginalJointLimits.lean:94`, `:118` | Time-first, then cutoff, to the same limit. |

## Scope and next mathematical obstruction

Nome, spatial width and the physical signed source probe remain fixed.
The time threshold is independent of late heat cutoff; the cutoff threshold
depends on the computed intermediate time. These are NOT spatial-volume or
lattice-spacing moduli. The selected chain action is not the action of the
entire ambient encoding box. Arbitrarily changing probes or cutoff-dependent
centering/covariance insertions are not covered by the fixed-probe theorem.

The one-sided limit is not yet a linear functional on a T-stable algebra,
a stationary law or a physical vacuum. A candidate next scalar route is:

1. Prove actual weighted symmetry ell(g*T f)=ell(f*T g), keeping both V
   factors in the double-slice Haar integral. The genuine relative word
   `BF4ExactSlabFixedSpatialKineticHeat.relative`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticHeat.lean:64`)
   and `SU2QuaternionHeadChainComposition.step_pairing`
   (`lean/YMGap/Continuum/SU2QuaternionHeadChainComposition.lean:97`)
   are existing ingredients, not this missing symmetry proof.
2. Multiply relative bracket certificates by certified terminal messages
   and prove the actual pairing denominator positive. This is intended to
   compare extensions of either side of an interior insertion.
3. Pin ell((T^m 1)*f*(T^n 1))/ell((T^m 1)*(T^n 1)) to the original
   middle-slice observable, retaining the middle spatial V exactly once.
   `BF4ExactSlabFixedSpatialChainAction.original_chain_pairing`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainAction.lean:102`)
   already accepts physical spatial probes, but the existing endpoint
   iteration theorem does not prove this interior split identity.

This is a source-reviewed next proof proposal, NOT checked two-sided
convergence or stationarity. Multi-insertion consistency and shift invariance,
connected correlations, physical reflected OS identification, actual completed
cutoff-limit operator power/moment compatibility, width/spacing-uniform
control, continuum QFT and the all-group physical gap remain open.

## Verification boundary

Two focused serialized one-worker/20 GiB checks passed all 15 public gates
within `{propext, Quot.sound}`. Fresh process/swap preflight preceded every
check; no competing compiler/test process was found, and recorded swap stayed
at 7085.19 MiB. The initial core check timed out elaborating expanded modulus
data; local irreducibility of existing modulus definitions resolved it without
raising heartbeat, memory or worker limits. Only the final successful logs
are claimed below. Independent read-only review found no mathematical or
statement defect in the rectangle or either iterated-limit identification.

Two selective-root imports were added. Root/full-tree/full axiom audit was
not run. No old declaration, canonical frontier field, literal hole, axiom
or analytic premise changed.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| BF4ExactSlabFixedSpatialOriginalJointCauchy | 9 | `0de85c086d8954b4d42feb4bfd2bf5f8023f725492ccd98a31f0fd744207a3f8` |
| BF4ExactSlabFixedSpatialOriginalJointLimits | 6 | `8ac8fa90192dbee3fe7ed06128b6af5e7ae5e6daf460c928942df7e797a4b802` |
