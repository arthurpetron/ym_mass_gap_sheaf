# Same-carrier reduced inverse and parallel downstream work

Date: 2026-09-16. Base checkpoint: `405acc5`, committed and pushed.
The preceding represented-row/relaxation goal turn is **PROGRESS**. This
checkpoint supplies actual proofs on the existing carrier, not new assumed
frontier fields. Source-only plans below are separated from checked results.

## Whole-project goal

For every compact simple gauge group, construct a nontrivial continuum
Yang--Mills theory on R^4 with the required QFT axioms, isolated vacuum and
positive physical Hamiltonian mass gap, constructively and Mathlib-free.
The group, action, observables, limiting theory and physical operators must
be identified throughout. **That target remains OPEN.** The current concrete
results concern fixed-spacing, small-nome SU(2).

## Mathematical contraction: an actual inverse, not assumed completeness

Write `N(x)=B(x,x)`, `C` for actual centering and `T_n` for actual discrete
time on `UnionCompletion`. The existing squared-norm estimate is
`N(T_n Cx) <= q(w)^n N(Cx)`, where the strictly positive `q(w)<1` is
`BF4ExactSlabFixedSpatialSpatialDenseGap.twoStepRate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`, and
`BF4SpatialUnionRelaxation.centered_norm_decay`,
`lean/YMGap/Continuum/BF4SpatialUnionRelaxation.lean:61`.

The short new argument is the exact weighted-square identity

```
r(1-r) N(x+y) + N(r*x-(1-r)*y) = r*N(x)+(1-r)*N(y).
```

Dropping the nonnegative square proves weighted Young's inequality without
square roots. With `r=q(w)` and `K=(1-q(w))^(-2)`, it closes the geometric-sum
induction using `N(T_2 y)<=q(w)^2 N(y)`. No fixed numerical upper guard on
`q(w)` is added. The actual series is `S_n x=sum_(j<n) T_(2*j)(Cx)`.

| Link | Declaration and source | Supplied result |
| --- | --- | --- |
| Explicit rational budget | `BF4SpatialUnionWeightedNorm.budget`, `lean/YMGap/Continuum/BF4SpatialUnionWeightedNorm.lean:34` | Positive denominator `(1-r)^2`; exact cancellation, no hidden beta-uniform constant. |
| Exact square identity | `BF4SpatialUnionWeightedNorm.norm_weighted_identity`, `lean/YMGap/Continuum/BF4SpatialUnionWeightedNorm.lean:130` | Uses the SAME completed bilinear form and rational operations. |
| Common finite-sum budget | `BF4SpatialUnionResolventPartial.partial_norm_bound`, `lean/YMGap/Continuum/BF4SpatialUnionResolventPartial.lean:118` | `N(S_n x)<=K*N(Cx)`, independent of sum length. |
| Actual tail | `BF4SpatialUnionResolventPartial.partial_tail_bound`, `lean/YMGap/Continuum/BF4SpatialUnionResolventPartial.lean:145` | Controls the actual difference of sums by relaxation on the SAME carrier. |
| Computed rows and rate | `BF4SpatialUnionResolventPartial.seriesModulus`, `lean/YMGap/Continuum/BF4SpatialUnionResolventPartial.lean:169`; `seriesRows`, same file:198 | The rate is `geometricCutoff q (K*normCap X) epsilon`; representatives are computed, not chosen. |
| Quotient-independent solver | `BF4SpatialUnionResolvent.resolventRepresentative_congr`, `lean/YMGap/Continuum/BF4SpatialUnionResolvent.lean:78`; `resolvent`, same file:87 | The represented-row diagonal descends to every existing completion class. |
| Convergence modulus | `BF4SpatialUnionResolvent.resolventModulus`, `lean/YMGap/Continuum/BF4SpatialUnionResolvent.lean:96`; `partial_resolvent_bound`, same file:99 | Original partial sums approach the constructed vector with an explicit squared-distance tolerance rate. |
| Two inverse identities | `BF4SpatialUnionResolvent.resolvent_right_inverse`, `lean/YMGap/Continuum/BF4SpatialUnionResolvent.lean:168`; `resolvent_left_inverse`, same file:184 | `(I-T_2)R=C=R(I-T_2)` on the actual union. |
| Constructive certificate | `BF4SpatialUnionResolvent.solutionCertificate`, `lean/YMGap/Continuum/BF4SpatialUnionResolvent.lean:193` | Returns the actual unit-complement vector, its equation and approximation modulus as Type-valued data. |
| Bounded inverse | `BF4SpatialUnionResolventBound.resolvent_norm_bound`, `lean/YMGap/Continuum/BF4SpatialUnionResolventBound.lean:143`; `resolvent_distance_bound`, same file:234 | Squared norm/distance bound `K(w)`; uniform in vectors, explicitly dependent on nome. |
| Rational linearity and time | `BF4SpatialUnionResolventBound.resolvent_add`, `lean/YMGap/Continuum/BF4SpatialUnionResolventBound.lean:182`; `resolvent_smul`, same file:201; `resolvent_time`, same file:211 | Exact identities, using uniqueness rather than choosing scalar representatives. |
| Original self-adjointness | `BF4SpatialUnionResolventBound.resolvent_selfAdjoint`, `lean/YMGap/Continuum/BF4SpatialUnionResolventBound.lean:222` | Equality in the actual completed pairing. |

The bound for the completed solver follows directly from its equation and
the weighted identity. `norm_budget_cancel`,
`lean/YMGap/Continuum/BF4SpatialUnionResolventBound.lean:96`, cancels only
the positive rational `q(w)*(1-q(w))^2`, never a possibly zero vector norm.
This avoids introducing a separate norm-limit or spectral-decomposition
assumption. The physical guards remain exactly `0<w<1`,
`heatRatio w<=half`, `heatRemainderBound w<1`, and
`entropyRate 625 (adjustedCoreRate w hd)<1`.

This is the reduced inverse of the discrete defect, not a construction of
`-log T`, a continuous-time semigroup, or a physical Hamiltonian. Full real
scalar structure and arbitrary quotient-valued sequence completeness are
not asserted. The canonical rational-GNSData/CReal-form mismatch remains
as recorded in `AUDIT-PARALLEL-FRONTIERS-2026-09-16.md`.

## Parallel results and the five requested work streams

All five areas admit independent upstream work, but their physical conclusions
must rejoin on one theory. The strict completed bound and a nonzero excitation
were already proved before this checkpoint; they are not pending blockers.
No meaningful percentage of the Clay problem follows from compiler counts.

| Requested area | Work performed / already available | Remaining independent work and rejoin |
| --- | --- | --- |
| Nonconstant excitation | Existing actual nonzero vector; new `BF4SpatialUnionOddEvenResponse.odd_response_le_even`, `lean/YMGap/Continuum/BF4SpatialUnionOddEvenResponse.lean:87`, and `lagTwo_floor_of_lagThree`, same file:96. | Old positive response has lag THREE, not two. Prove the explicit original-action finite comparison supplying the current lag-three floor; then the checked inequality supplies lag two. Continuum survival remains separate. |
| Full Hilbert/OS/QFT | Constructed the bounded same-carrier solver above, using the previous represented-row limit machinery. | Full real scalar structure, gauge-observable coverage, full spatial action, continuous-time reconstruction and canonical same-functional OS pins remain open. The inverse is a functional-analysis component, not the full QFT package. |
| Spatial and spacing control | New `BF4SpatialUnionDiagonalTranslation.completedInner_translate`, `lean/YMGap/Continuum/BF4SpatialUnionDiagonalTranslation.lean:268`, proves actual pairing preservation; `completedTranslation_time`, same file:239, proves actual-time commutation. | This is a positive diagonal natural semigroup only. Signed independent-axis action and changing-action/spacing estimates remain open. The old small-nome AF guard obstruction is unchanged. |
| Positive physical mass calibration | Reviewed existing scalar exact-log, spacing and fixed-distance compilers; no duplicate wrappers added. | Actual-transfer/physical-length identification, scale-compatible contraction and finite upper rate control are physical inputs still missing. See `AUDIT-PARALLEL-SPACING-MASS-2026-09-16.md`. These are independently investigable, not consequences of this inverse. |
| Every compact simple group | Reviewed global forms, constructive quotient/descent and second-group representation/tail data; generic completion infrastructure is reusable. | Actual group/representation/Haar/action producers remain required. The existing spin-half observable is rejected for the SO(3) global-form code. See `AUDIT-PARALLEL-ALL-GROUPS-2026-09-16.md`. No new non-SU(2) physical instance is claimed. |

Four concurrent lanes were used: parent partial-sum/solver construction; a
weighted-estimate/bounded-inverse author; a spatial-translation author and
independent source reviewer of the solver; an excitation/response reviewer
and odd/even-inequality author. Compilation remained serialized by the parent.
The independent mathematical source review found no substantive defect in
the weighted estimate, partial sums, solver or completed bound; in particular,
it checked the `q^2` versus `q` distinction and the positive-scalar cancellation.

The spatial proof uses the exact identities
`paddedWidth (b+2*s) r = paddedWidth b (r+s)` and literal
`recenter r (translate s x)=recenter (r+s) x`. The new pairing sequence is
therefore a cofinal shift, not a different finite action assumed equivalent.
The precise scope and source map are in
`AUDIT-UNION-SPATIAL-TRANSLATION-FRONTIER.md`.

The response review corrected the older excitation audit rather than hiding
the time offset. Sections 1–4 of
`AUDIT-UNION-POSITIVE-RESPONSE-FRONTIER.md` are a quantitative proof plan,
not checked geometry or a supplied positive floor. Section 5 records the
checked odd/even reduction, which does not assume positivity of one-step time.

## Verification boundary

All six new modules passed focused checks, each with one monitored worker,
20 GiB hard worker limit and fresh process/swap inspection. Final logs contain
92 printed public axiom gates, only `{propext, Quot.sound}`, and no errors,
warnings, `sorryAx` or `Classical` dependency. No previous proof or canonical
field was changed, and no sorry, axiom, noncomputable choice or stronger
analytic premise was added. Root imports were added; the root, full tree and
full audit were NOT run. No safety limit was raised; CI remains manual-only.
No routine literature scan was performed.

The standard focused command was:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/NAME.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/NAME.olean \
  --log-file /tmp/LOG
```

| Module under `lean/YMGap/Continuum/` | Gates | Final log under `/tmp/` | Source SHA-256 |
| --- | ---: | --- | --- |
| `BF4SpatialUnionWeightedNorm.lean` | 8 | `ym-union-weighted-norm-20260916.log` | `11b8bdc94e246f317717b513a9b0b3b8603ca5933cb9ac051e79a4b0c28d41e8` |
| `BF4SpatialUnionResolventPartial.lean` | 18 | `ym-union-resolvent-partial-20260916.log` | `16dd0354d7f01f6f503d62bf9cdf06607d09d914f3655dd137a21df607381324` |
| `BF4SpatialUnionResolvent.lean` | 16 | `ym-union-resolvent-20260916.log` | `8501830ee00a89d4be5ee8a922cd92bf6574ccb9c056466baf0ec687ffbe94bd` |
| `BF4SpatialUnionResolventBound.lean` | 17 | `ym-union-resolvent-bound-20260916.log` | `b3dba9a77ad809bd29bf1b5dd70363578f0bb9ec82258a8fd66a39dc3849cf4b` |
| `BF4SpatialUnionDiagonalTranslation.lean` | 29 | `ym-union-diagonal-translation-20260916.log` | `d0e828d8a6c9754ca32580cd57a68cb2b6bf3b17eea233d61396945bfa01ee9a` |
| `BF4SpatialUnionOddEvenResponse.lean` | 4 | `ym-union-odd-even-response-20260916.log` | `434fa3ee8d5dc215474e12f46a181da8a78b1af7d9741657e23ce7695c23dfab` |

## Next bounded mathematical task

Implement the response plan's actual translated-full-box placement,
selected-chain inclusion, omitted-face separation and probe pins. The
existing signed boundary comparison and cutoff-uniform numerator floor then
have concrete missing inputs, rather than a new bundle assuming the desired
correlation bound. Keep the old/current finite actions and lag-three/lag-two
distinction explicit. Real scalar and full spatial-action work may continue
independently; continuum and all-group analytic producers must remain visible
as unproved requirements of the unchanged whole-project goal.
