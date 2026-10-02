# Original physical bulk correlation comparison

The source references and verification hashes below record checkpoint
`8571e62`. The subsequent spatial-limit join is recorded separately in
`audits/AUDIT-ORIGINAL-BULK-SPATIAL-LIMIT-2026-10-02.md`.

## Result and scope

The CURRENT original physical bond correlations of the same finite signed
sources now agree across independently constructed padded widths to a computed
tolerance. This fills a fixed-coupling scalar comparison after the full literal
width map was refuted; it does not construct a replacement vector map.

`bulkConnected_inclusion_close`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:369`) bounds
disagreement by epsilon in both directions. Both widths retain their OWN means.
Its hypotheses include `0<w<1`, `base>0`, `base<=larger`, and ALL three existing
guards: `heatRatio w<=1/2`, `heatRemainderBound w<1`, and
`entropyRate 625 (adjustedCoreRate w hd)<1`. Source support and lag are fixed,
with `x.radius+1<=H` and `y.radius+lag+1<=H`. This is original SU(2) lattice
time, not a nome-, spacing- or all-lag-uniform theorem.

## Mathematical argument

The existing actual original-action producer is
`BF4ExactSlabFixedSpatialWilsonBaseCoherence.chartScalar_inclusion_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonBaseCoherence.lean:129`).
It retains both partitions. For a window e the error is
`B_e = A_e * q^(r+1-S)`, with A_e the existing `spatialAmplitude`, q the
entropy rate, and S the source-box `carrierSize`. The larger width, heat stage
and exterior-time depth do not enter this budget.

`expectation_diagonal_converges`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:67`) reaches the
CURRENT fixed-width original joint limit via `chartScalar_original_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:127`)
and `originalJoint_diagonal_converges`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:122`).
The synchronized raw sequences converge with their respective moduli;
their independently regularized approximants are not identified.

The three-moment error is
`B_joint + cap(left)*B_right + cap(right)*B_left`.
`finite_connected_inclusion_bound`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:154`) retains all
six moments and obtains the two endpoint caps from the actual positive action
using `finiteValue_abs_bound`
(`lean/YMGap/Continuum/BF4ExactSlabAllNomeFiniteMomentBounds.lean:61`).
`connected_inclusion_bound`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:211`) passes this
same bound through original heat/time removal. `connectedAmplitude`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:141`) returns the
full source-sized budget as rational data. `comparisonModulus`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:249`) returns
`S+geometricCutoff(q,connectedAmplitude,epsilon)` as Nat data;
`connected_inclusion_close`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:255`) controls
every later spatial collar, independently of the larger width.

## Physical identification

`connectedMoment`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:113`) is a generic
three-moment subtraction, not by itself a covariance claim. The physical
consumer supplies joint `crossOdd x (advance lag y)`, left
`crossOdd x (unit base)`, and right `crossOdd (unit base) y`.

`bulkSource_crossOdd`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:290`) preserves
the source radius, reflection, signed terms, offsets and central extra step.
`bondForm_bulkSource_pin`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:303`) pads native
odd horizons into a common comparison horizon ONLY AFTER the original joint
limit, with zero time shift. No finite symmetric-depth equality is used.
`bulkConnected_pin`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:325`) invokes
`connected_source_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSConnectedDecay.lean:110`).
Thus the final theorem bounds ACTUAL BondCompletion correlations with both
OWN vacuum means and the full lag+one buffer, not an unreflected product
covariance or an assumed quotient/vector map.

## Verification

Final focused check on 2026-10-02 UTC exited 0 without warnings or errors:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.olean --log-file /tmp/ym-original-bulk-comparison-20261002-final.log
```

All twenty-two printed gates lie within {propext,Quot.sound}; the elementary
two-sided order helper uses only propext. No sorryAx, new axiom, classical
choice, native proof oracle, erased witness or weakened frontier. Independent
Sol mathematical/source review passed. Memory pressure reported 86 percent
free before and after checks; swap remained zero. One monitored 20 GiB capped
worker and a 12 GiB OS reserve were used; no competing compiler/test/runner
was found before checking.

- Source SHA256: `d1ecdf3d92bba01d9b0e41e59ef5d6d53ad1bb4c8fd2bbcca36602c12568cec1`.
- Final log SHA256: `6b1335e0a736d61d104f86d1aedb7ef73500f00ce1cb19e59e4b7158c116d6c4`.
- One semantic root import added. Full root/tree build, full audit, guard and
  progress checks were NOT run; the focused check is the verification boundary.
- CI remains manual-dispatch only. The canonical ASCII chart is unchanged;
  no exact displayed claim closed and no chart was reprinted.

## Remaining frontier

Join these controlled CURRENT physical bulk correlations to the existing
fixed-coupling spatial functional, preserving sources and time. The small-nome
rate does not give control along a justified changing-spacing family or toward
nome one. Complete signed temporal energy/OWN-variance control, physical mass
calibration, nontrivial continuum survival, full same-theory QFT and every
compact simple group remain OPEN.
