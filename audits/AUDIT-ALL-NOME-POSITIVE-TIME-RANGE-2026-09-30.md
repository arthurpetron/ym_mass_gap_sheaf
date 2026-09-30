# Original positive-time range: constructive polynomial approximation

Date: 2026-09-30 UTC. Status: three focused Lean checks passed; no broad run.
Whole-project goal: constructive continuum Yang--Mills on R^4 for every
compact simple group, with the same-theory QFT axioms and a positive finite
physical mass gap. That goal remains OPEN.

## Mathematical increment and actual consumer

The width-one boundary kernel previously disproved full-carrier injectivity
of the original all-nome Wilson time operator. The new construction instead
takes a supplied original vector x and approximates its actual image T x by
actual T^2-images. No preimage is selected and no state is discarded.
All operators and pairings act on
`BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width`, for every
rational nome 0<w<1. T is the original completed ONE-step time operator.

Write D=I-T and m(k,l)=B(x,T^k D^l x). The proofs establish

```
m(k,l) >= 0,
m(k,l) = m(k+1,l) + m(k,l+1),
(n+1) m(k+1,l+n) <= m(k,l),
||D^n T x||^2 = m(2,2n) <= ||x||^2/(n+1)^2.

u_n = sum_{j<n} D^j x,
T^2 u_n + D^n T x = T x.
```

The first row bound is a finite telescoping argument retaining the last
nonnegative term. Applying it twice proves the squared rate. The finite
polynomial u_n is the actual consumer: `positiveTimeRangeApproximation`
returns it as data, with relative squared error at most epsilon at the
computed index `relativeTailModulus epsilon = epsilon.den`. This cutoff
is sufficient, not asserted optimal.

The only new positivity argument beyond the existing time laws is short.
Set a=B(x,Tx), b=B(Tx,Tx), c=B(Tx,T^2x). Positivity at x-Tx gives
a-2b+c>=0; the upper time-form bound at Tx gives b-c>=0. Adding proves
a-b>=0, i.e. positivity of T(I-T). Symmetry and commutation then peel two
powers at a time, reducing all mixed moments to the four positive forms
I, T, D, TD. No spectral theorem or square root is used.

## Declaration evidence

Paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Exact scope |
| --- | --- | --- |
| `completedTime_form_le` | `BF4WilsonAllNomeTimeDefectMoments.lean:120` | Actual time form bounded by original squared norm. |
| `defect_nonnegative` | `BF4WilsonAllNomeTimeDefectMoments.lean:164` | Positivity of I-T. |
| `time_defect_nonnegative` | `BF4WilsonAllNomeTimeDefectMoments.lean:171` | Positivity of T(I-T). |
| `mixedMoment_nonnegative` | `BF4WilsonAllNomeTimeDefectMoments.lean:343` | Every completed vector and both arbitrary natural powers. |
| `mixedMoment_split` | `BF4WilsonAllNomeTimeDefectMoments.lean:349` | Exact same-operator positive split. |
| `mixedMoment_telescoping_budget` | `BF4WilsonAllNomePositiveTimeTail.lean:69` | Finite row budget with positive final term retained. |
| `mixedMoment_row_bound` | `BF4WilsonAllNomePositiveTimeTail.lean:86` | Inverse-linear moment bound. |
| `positiveTimeTail_norm_pin` | `BF4WilsonAllNomePositiveTimeTail.lean:115` | Filter norm equals original mixed moment m(2,2n). |
| `positiveTimeTail_bound` | `BF4WilsonAllNomePositiveTimeTail.lean:126` | Original squared norm times 1/(n+1)^2. |
| `relativeTailModulus`, `tailRate_small` | `BF4WilsonAllNomePositiveTimeTail.lean:133`, `:135` | Explicit natural cutoff and rational bound. |
| `positiveTimeTail_small` | `BF4WilsonAllNomePositiveTimeTail.lean:147` | Relative squared-norm tolerance on the same carrier. |
| `inverseSum` | `BF4WilsonAllNomePositiveTimeRange.lean:42` | Explicit original-vector polynomial. |
| `inverseSum_twoStep_identity` | `BF4WilsonAllNomePositiveTimeRange.lean:59` | Exact telescoping join to T x and T^2 u_n. |
| `inverseSum_error_bound` | `BF4WilsonAllNomePositiveTimeRange.lean:75` | Actual approximation error, with the squared rate. |
| `positiveTimeRangeApproximation` | `BF4WilsonAllNomePositiveTimeRange.lean:84` | Witness-bearing approximation, not a Prop-level existence claim. |

## Honest boundary and next work

- Uniformity ranges over the explicitly named nome and width parameters
  and every original completed vector. n counts polynomial filter
  iterations, NOT physical time or lattice refinement. No mass scale or
  positive lower response is inferred from this uniform coefficient.
- The argument is positive-contraction algebra, not a non-abelian coercivity
  mechanism. It gives no abelian or non-abelian mass-gap claim.
- It does NOT prove D^n x tends to zero for every x, density of the range
  in the full carrier, a full-carrier inverse, a representing spectral
  measure, continuous time, or an unbounded Hamiltonian. The positive-norm
  boundary kernel is unchanged.
- There was no existing all-nome Hausdorff-representation consumer found
  in the targeted source review. Here the actual new consumer is the
  quantitative original-range approximation, not an assumed future
  reconstruction. Further functional calculus must respect its restricted
  input T x; it cannot silently promote that input to an arbitrary vector.
- The useful original-action signed/collective estimate along a justified
  scaling family remains the analytic priority. The conditional-link
  generator is still distinct from OS time. Spatial/spacing control,
  continuum survival, physical calibration, full QFT and every-group
  construction remain open. No canonical frontier field was changed.
- Source review found that positive spatial-limit norm and lag-two response
  were ALREADY proved at the fixed small nome; they were not rebuilt.
  `BF4ExactSlabOriginalResponseNumeratorFloor.original_numerator_floor`
  (`.lean:43`) imports the fixed-nome signed remainder budget before the
  generic spatial comparison. Parameterizing that genuine analytic budget
  is not accomplished by the present operator-algebra result.

## Verification and coordination

Sol constructed the mixed-moment module. Root proved the tail and its
polynomial range consumer. Luna independently reviewed the two estimates,
telescoping sign and scope; Sol also reviewed the final consumer argument.

Final checks used, sequentially, for each of the three files:

```
python3 scripts/safe_lean_build.py --jobs 1 --status-seconds 300 \
  --check-worker-limit-gib 20 --check lean/YMGap/Continuum/FILE.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/FILE.olean \
  --log-file lean/.lake/LOG.log
```

| File | Final result | Printed gates |
| --- | --- | --- |
| `BF4WilsonAllNomeTimeDefectMoments.lean` | exit 0, 9.11 s | 16 |
| `BF4WilsonAllNomePositiveTimeTail.lean` | exit 0, 2.40 s | 10 |
| `BF4WilsonAllNomePositiveTimeRange.lean` | exit 0, 2.06 s | 6 |

All 32 reported axiom sets are subsets of {propext, Quot.sound}; the
relative cutoff definition is axiom-free and its rational rate proof uses
only propext. Earlier local elaboration errors (core natural induction and
notation) were repaired before these final passing checks. No sorry was
introduced or discharged, and no new analytic premise or axiom was added.

Preflight found 79% pressure-free memory and no competing compiler/test/
runner process. One worker, 20 GiB ceiling, OS reserve and continuous
automatic safety monitoring remained enforced. All checks finished in their
initial calls; no live-job polling loop was needed. Status output is set
to five minutes without slowing automatic safety monitoring.

Three semantic-root imports were added. Full-root/full-tree build, full
axiom audit, guard and broad tests were NOT run. Source whitespace and
new-file prohibited-token checks passed. The canonical ASCII chart's
displayed proof states are unchanged, so it is not reprinted.
