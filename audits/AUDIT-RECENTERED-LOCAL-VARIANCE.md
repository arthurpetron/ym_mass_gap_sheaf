# Recentered original plaquette variance without volume loss

Date: 2026-09-16. PROGRESS after `c7729d4`.

WHOLE-PROJECT GOAL: construct nontrivial continuum quantum Yang--Mills
on R^4 with the required QFT axioms and a positive physical Hamiltonian
gap for EVERY compact simple group, within the constructive axiom gate,
with all conclusions tied to the SAME theory. That goal remains open.

## Mathematical contraction

At arbitrary fixed `0 < w < 1`, let A be any duplicate-free selection of
physical heat factors, at cutoff K >= headCutoff(w). Choose an actual edge
of a physical plaquette, and write A=S*R, where S contains exactly the
selected factors touching that link. The remaining product R retains ALL
other selected interactions. Four-dimensional geometry gives |S| <= 6.

Write H for the original product quaternion-Haar functional and chi for
the original fundamental plaquette character (integer label one). Exact
single-link character selection, with the proved link-independent R,
gives H(chi*R)=0 and H(chi^2*R)=H(R). Consequently, for every rational c,

    H((chi-c)^2*R) = (1+c^2)*H(R) >= H(R).

The existing certified local heat comparison yields

    H(A*(chi-c)^2) >= L*H(R),    H(A) <= U*H(R),
    delta(w) = L/U = starRatio(w) > 0,

where L=min(headFloor(w),1)^6 and U=(1+prefixCap(w))^6. No spectator
mass is divided out. Divide by the positive ORIGINAL H(A) and choose c
to be its actual rational interacting mean. The result is

    E_A[chi^2] - E_A[chi]^2 >= delta(w).

The observed face need not belong to the selected action. The link must
be an actual edge of that physical face; the selected IDs must be physical
and duplicate-free. Those hypotheses are retained, not assumed away.

This removes the previous whole-volume floor/cap loss from this particular
nontriviality witness. It does NOT improve the transfer contraction rate.
The floor depends on w; no uniform coupling/spacing assertion is made.

## Original chart, limits and completed vectors

An arbitrary spatial face gives a literal radius-zero signed presentation.
Its reflected square and first moment are pinned to the SAME original
finiteValue action, partition, cutoff stage and shifted ambient face:

    extent = adjacentEvenExtent(width+t),
    selected action = chainIds extent width (width+1) (t+t),
    face = timeShiftPlaquette ((width+1)+t) p.

The finite variance bound applies for every stage and t, including zero.
The actual stage=depth=k joint diagonal converges; multiplication continuity
and limit order pass delta(w) to jointCenteredMoment(0,x,x). The existing
explicit-modulus centering stream realizes this scalar as B(c(x),c(x))
in the SAME JointCompletion. Positivity of delta proves c(x) is not the
embedded zero, without assuming unproved completed positive definiteness.
Its time pairings retain the original connected-correlator pin.

Translation by margin+1 in each spatial coordinate, into the computed width
`width+2*margin+2`, puts every actual plaquette-edge endpoint at margin at
least the requested value. It preserves temporal radius and commutes with
physical time advance. Applying the preceding construction in each target
box gives a recentered family with the SAME positive self-pairing floor.
Different widths still have separate carriers and states: no cross-width
isometry, state convergence or limiting vector is asserted.

## Declaration evidence

All module paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Verified role |
|---|---|---|
| `starRatio`, `starRatio_positive` | `BF4ExactSlabLocalStarComparison.lean:46`, `:65` | Existing explicit nome-dependent local constant and positivity. |
| `selectedStar_length_le_six` | `BF4ExactSlabSelectedStarVariance.lean:78` | Actual geometry and no-repetition guard. |
| `selected_heat_partition`, `rest_character_zero`, `rest_square_moment` | `BF4ExactSlabSelectedStarVariance.lean:91`, `:121`, `:134` | Exact action decomposition and retained-background character moments. |
| `selected_star_bounds`, `shifted_square_floor` | `BF4ExactSlabSelectedStarVariance.lean:220`, `:256` | Local comparison and all-rational-center squared cost. |
| `normalizedVariance_floor`, `finiteValue_variance_floor` | `BF4ExactSlabSelectedStarVariance.lean:320`, `:366` | Original mean and SAME original reciprocal/partition. |
| `faceSpan`, `placedSpan_character` | `BF4ExactSlabFixedSpatialFaceCharacter.lean:70`, `:97` | Arbitrary valid face and literal ambient placement. |
| `chartScalar_mean_finiteValue`, `chartScalar_square_finiteValue` | `BF4ExactSlabFixedSpatialFaceCharacter.lean:126`, `:147` | Common-action first/second moments. |
| `recenter`, `recenter_radius`, `recenter_time` | `BF4ExactSlabFixedSpatialSpatialRecenter.lean:91`, `:96`, `:99` | Computed translation preserving time geometry. |
| `recenter_face_inset`, `recenter_inset` | `BF4ExactSlabFixedSpatialSpatialRecenter.lean:109`, `:127` | Every actual edge endpoint has the requested spatial margin. |
| `chart_variance_floor`, `face_variance_converges`, `face_joint_variance_floor` | `BF4ExactSlabFixedSpatialLocalVariance.lean:61`, `:96`, `:111` | Finite bound, same joint diagonal, limiting original variance. |
| `faceExcitation`, `faceExcitation_norm_floor`, `faceExcitation_ne_zero`, `faceExcitation_correlator_pin` | `BF4ExactSlabFixedSpatialLocalVariance.lean:126`, `:129`, `:136`, `:149` | Actual centered completed vector, self-pairing floor, nonzero proof and physical-time correlator. |
| `bulkExcitation`, `bulkExcitation_norm_floor` | `BF4ExactSlabFixedSpatialLocalVariance.lean:160`, `:166` | Actual recentered family with one positive floor independent of width/margin. |

Here `norm_floor` always means the displayed self-pairing/squared-norm
bound, not a bound on an independently constructed unsquared norm.

## Next causal frontier: source review, not new proofs

The next exact comparison needs translated selected-chain numerator and
partition pins in one common ambient Haar carrier. The new geometric map
does not prove those identities. Then the actual omitted spatial faces must
be separated from the translated probe support, uniformly as temporal
buffers grow. The current fixed-width time limit alone supplies no such
spatial modulus.

There is already an arbitrary-mask analytic consumer under SMALL-NOME
guards, not only a complete-slab specialization:

- `lean/YMGap/Continuum/BF4ExactSlabUniformCoreBudget.lean:103`,
  `mixedNumerator_tail_bound`, accepts any duplicate-free physical ambient
  ID list and any keep mask. It requires `heatRatio w <= 1/2`,
  `heatRemainderBound w < 1`, and
  `entropyRate 625 (adjustedCoreRate w hd) < 1`, together with actual
  interval, locality, probe-carrier and active-core size data.
- `lean/YMGap/Continuum/BF4ExactSlabCoreDistanceFloor.lean:56`,
  `active_core_linf_floor`, converts actual omitted-face separation into
  `distance+1 <= probe.animal.support.length+anchor.length`.
- `lean/YMGap/Continuum/BF4ExactSlabFaceSetBoundaryComparison.lean:125`,
  `mask_tail_bound`, consumes these data for normalized mask comparison.
  `lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:64`,
  `comparison_bound_eventually`, is the all-nome normalized consumer of
  a supplied finite determinant estimate; it does not produce that estimate.
- `lean/YMGap/Continuum/BF4ExactSlabSummableCoreRate.lean:37`,
  `existingNome_entropyRate`, certifies the existing pilot's entropy guard,
  not arbitrary nome. Do not silently add this guard to an all-nome theorem.

For unrestricted nome, the signed three-mark response/cofactor estimate
remains an analytic obstruction. The response identity retains its third
cumulant and negative pair-product correction
(`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:90`,
`response_identity`); the quantitative premise in the same file at line
224, `covariance_response_bound_eventually`, remains unsupplied here.
No paper scan or external result was used to discharge it.

Full completed Hilbert/OS/QFT structure, spatial and spacing passage,
width-independent decay, physical time/mass calibration, continuum
nontriviality and the all-group target remain open. No canonical frontier
field was inhabited or weakened, and no sorry or axiom was added or removed.

## Verification boundary

Four focused final module checks passed, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`, each with
its own fresh process/swap preflight. All 39 public printed gates reported
only subsets of {propext, Quot.sound}. Initial development checks exposed
projection-normalization, a notation collision, and avoidable large-term
unfolding; these were corrected before the final successful checks.
One scalar algebra proof has a scoped 2,000,000 heartbeat budget; memory
limits, worker count and safety thresholds were not raised.

The safe-build skill kept verification narrow and serialized. Independent
read-only review checked spectator exclusion, normalization, joint-limit
direction, same-carrier centering and spatial endpoint margins. No full
root build, full-tree build or full axiom audit ran. Four selective-root
imports were added, but that root itself was not recompiled.

| Checked module | Public gates | Final log SHA-256 |
|---|---:|---|
| `BF4ExactSlabSelectedStarVariance` | 8 | `0974a0c2345e548c902cdcbb17c9456f926bf8b098f2d57465c22421b3d5f23b` |
| `BF4ExactSlabFixedSpatialFaceCharacter` | 5 | `733f1c840696519c7021898294211703af6166a791e847990d6c0e65c235a1f6` |
| `BF4ExactSlabFixedSpatialSpatialRecenter` | 16 | `c7565c92285fb81a5c6397653106395b39b428933d4ab80182917d7068ef2ad6` |
| `BF4ExactSlabFixedSpatialLocalVariance` | 10 | `c88209ccf37f078bb32ffb7dd25d83d5b11d55593f69ba089da2000252507f45` |

Local log paths: `/tmp/ym-selected-star-variance-20260916.log`,
`/tmp/ym-face-character-20260916.log`, `/tmp/ym-spatial-recenter-20260916.log`,
and `/tmp/ym-fixed-spatial-local-variance-20260916.log`.

Literature policy remains at most one routine listing scan per 12 hours.
The last completed scan was 2026-09-16 09:54 UTC; optional refresh is not
before 21:54 UTC. Reuse `audits/RESEARCH-MATH-PH-2026-09-16.md` between
scans; it contains findings, not a complete abstract archive. No scan was
performed for this checkpoint.
