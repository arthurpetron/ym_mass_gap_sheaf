# Complete signed multiplication cost: original source and SAME limit

The unchanged goal is nontrivial continuum Yang--Mills on R^4 for every
compact simple group, with SAME-theory QFT axioms and a positive physical
Hamiltonian mass gap. It remains OPEN. This increment controls one complete
signed component of the existing original block split, not its relative
scaling estimate.

## Exact original source and normalization

Let T be the original finite transfer, ell its original spatially weighted
Haar functional, g_n=T^n 1, and c_n the actual OWN odd-window mean of f.
Set

    psi = f-c_n,  A = g_(n+t),  b = T^t(g_n*psi),
    Z0 = ell(A^2), Z1 = ell(A*T A),
    D(A,h) = Z1*ell(h^2)-Z0*ell(h*T h).

The existing COMPLETE signed multiplication cost S satisfies

    S = D(A,b)-D(A,A*psi).

Both distinct positive partitions Z0 and Z1 are retained in S/(Z0*Z1).
The first cleared-cost window has depth n and lags 2t,2t+1; the second
has depth n+t and lags 0,1, STILL with center c_n. It is not recentered at
c_(n+t). In each lag difference c_n^2 cancels exactly. Endpoint-mean
errors are paid by

    q^n*(2C)^2 + q^(n+t)*(2C)^2,
    q=mixRate(w,width)<1, C=polynomialCap(f).

This is a finite identity and two-sided error estimate for the original
interacting source. No stationary finite terminal or replacement action,
mean, denominator or limit is used.

## Favorable limit, with explicit onsets

For the literal fundamental source loop, four EXISTING chronological joint
limits give the limit of this normalized source:

    L_t = (Joint_(2t)-Joint_(2t+1))-(Joint_0-Joint_1)
        = (C_(2t)-C_(2t+1))-(C_0-C_1)
        = M(v,2t,1)-M(v,0,1) <= 0.

Here v is the EXISTING completed centered loop vector, C_j=<v,T(j)v>
on its SAME carrier, and M is the existing mixed time/defect moment.
The stationary mean square cancels between adjacent chronological joints.
The favorable sign follows from existing mixedMoment_time_decreasing;
it is proved, not assumed.

For tolerance epsilon>0 put delta=epsilon/16. Three Type-valued onsets
are explicitly constructed:

- cutoff: maximum of the four jointCutoffThreshold values at delta;
- exterior depth: maximum of their jointTimeThreshold values and
  geometricCutoff(q,(2C)^2,delta);
- representative: maximum of delta.den and their jointModulus values.

The two source approximation orders each cost at most 6delta: four raw
joint errors and two geometric mean errors. QMhat_directed transfers the
completed sign to the selected representative with cost 5delta and onset
delta.den. The existential eventual-order witness is used only inside a
Prop proof; no witness is extracted into Type. Consequently EVERY source
in the independent late cutoff/depth rectangle satisfies

    S/(Z0*Z1) <= 11delta <= epsilon.

The diagonal converges to L_t with the computed maximum of cutoff and
depth onsets and the separate representative onset. Nome, width, source
loop and smoothing lag are fixed in each convergence statement; their
dependence is retained in the onset definitions.

## Remaining analytic input

This is NOT all-depth finite nonpositivity, a useful relative bound versus
ell(b^2), a family-uniform onset, or continuum/Clay closure. It pays the
complete signed component, not the combined original energy and cost.

Writing delta_j=C_j-C_(j+1), the sign only gives delta_(2t)<=delta_0.
It does not give delta_(2t)<=C*C_(2t)/(2t). Dropping the favorable signed
term may discard the large cancellation needed when initial energy is
large. Retain its magnitude in the combined original estimate, or produce
an initial-energy estimate against the SAME filtered variance, or the
existing retained macroscopic-response ratio, on a JUSTIFIED changing family.
No such analytic producer is supplied by this increment. Spatial/spacing
control, continuum survival, physical calibration, full QFT structure,
every group and the Clay endpoint remain OPEN.

## Declaration anchors

All paths below have prefix `lean/YMGap/Continuum/`.

- `BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:204`,
  `signedMultiplicationCost_difference`; :244, `original_block_rayleigh_split`.
- `BF4ExactSlabFixedSpatialSignedMultiplicationWindow.lean:55`,
  `originalPartitionProduct`; :60, `originalPartitionProduct_positive`;
  :72, `normalizedSignedMultiplicationCost`; :87, `original_signed_window_pin`;
  :139, `centered_lag_raw_bounds`; :204, `original_signed_raw_bounds`.
- `BF4WilsonAllNomeSignedMultiplicationLimit.lean:67`, `signedCostLimit`;
  :117, `signedCostLimit_completed_pin`; :132, `signedCostLimit_nonpositive`;
  :174, `signedCostLimit_representative_bound`; :210, `signedCostCutoffOnset`;
  :218, `signedCostDepthOnset`; :229, `signedCostRepresentativeOnset`;
  :275, `original_signed_joint_approx`; :328, `original_signed_eventual_upper`;
  :349, `original_signed_diagonal_converges`.
- Existing `BF4WilsonAllNomeDyadicChronologicalResponse.lean:68`,
  `centeredTimeMoment_chronological_pin`;
  `BF4WilsonAllNomeCenteredVector.lean:159`, `centeredVector_time_pairing`;
  `BF4WilsonAllNomeTimeDefectTail.lean:63`, `mixedMoment_time_decreasing`.
- Existing `BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:136`,
  `originalJoint_approx`; `GNSHilbertSpace.lean:184`, `QMhat_directed`;
  `PositiveContractionResidual.lean:119`, `geometricCutoff`; :126,
  `geometric_bound`.
- Existing conditional alternatives:
  `BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:102`, `temporalEnergy_linear`;
  `BF4WilsonAllNomeMacroRatioFilteredCost.lean:123`, `macro_to_filtered_budget`.

## Verification evidence

All three final serialized focused checks exited zero. Their 24 printed
gates (16 new, eight unchanged) depend only on {propext, Quot.sound}.
Accepted logs contain no errors, warnings, sorryAx or PANIC. The failed
development limit log a is excluded: a missing direct import, case-lambda
layout and congrArg beta-reduction rewrite were corrected without changing
any statement, estimate or resource limit.

Every launch uses a fresh memory/process/swap preflight and the monitored
safe launcher: one worker, 12GiB reserve, 20GiB worker ceiling. Fresh
preflights showed 83--84% free memory, zero swap and no competing proof job.
No limit increase, concurrent heavy job, full build, aggregate root, broad audit/guard
or progress metric is used. Root imports are registration-only.

| Source basename | Accepted log under /tmp | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `BF4ExactSlabFixedSpatialBlockRayleighSplit.lean` | `ym-signed-multiplication-split-20261003-a.log` | 9 | `e44e192a07e8e60020cb3ee395987b89050f999b629278dbb519b85d1b7190b9` | `ddaf9b0a1a77a60fba57bd1ff611b666e8d7e793b1a5158b49e5c5f7dc0758f1` |
| `BF4ExactSlabFixedSpatialSignedMultiplicationWindow.lean` | `ym-signed-multiplication-window-20261003-a.log` | 5 | `aa6becb38fe4dd9fd32a21d0d5c1b663a8841edf21b98c14bebfa26b196e2598` | `0768d1820c528d874edc1fca33f4771b2a84b15fdb4ef6c42a93e957f66a7480` |
| `BF4WilsonAllNomeSignedMultiplicationLimit.lean` | `ym-signed-multiplication-limit-20261003-b.log` | 10 | `b81ecd5053c7b25d5331c7ba5e8475e02d0749280c785a7c3fba55094efc78d0` | `8d166f1fe05c633bd67d4a378da3e3f054acb74c75454158a0771e9fbdf6b873` |

Root read all three full sources; independent Sol mathematical/source review
passed the two partitions, unchanged moving center, original limit/carrier,
sign orientation and explicit onsets. Reviews are not kernel checks.
The older split gained only a public export of its existing private identity
and that export's axiom gate. No sorry, axiom, classical shortcut or resource
option was introduced. CI remains manual-only. The canonical first chart
fence is unchanged, SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`;
this fixed-parameter component does not close an exact
displayed scaling claim, so no ASCII chart is reprinted.

Independent Luna final evidence/documentation QA passed all six hashes,
24 accepted gates, current declaration anchors, unique imports, explicit
fixed-parameter/relative-bound boundary, unchanged first chart fence and
manual-only CI. Staged diff whitespace checks passed.
