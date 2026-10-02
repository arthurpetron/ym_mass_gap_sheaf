# Original physical bulk correlations at the spatial limit

## Result and scope

The CURRENT completed physical bond correlations now approach the existing
reflected spatial connected value with an explicit geometric error and a
computed spatial tolerance modulus. The estimate also holds uniformly in
every larger ambient width, with the SAME smaller-source target and modulus.
This joins actual independent physical carriers to an existing scalar limit;
it does not construct a map between those full carriers.

`bulkConnected_spatial_close`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:588`) compares
the actual correlation to the quotient of `spatialConnected`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:558`). If F is
the existing small-nome `intrinsicForm`, the target is
`F(x,advance(lag+1)y) - F(x,u)*F(u,y)`. Both finite-width OWN means and the
extra one-step bond clock are retained.

`bulkConnected_included_spatial_close`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:628`) gives
the same two-sided epsilon bound for the included physical correlation at
ANY `larger>=base`. The threshold is the existing smaller-source
`comparisonModulus` (same module, line 261) at epsilon/2. Neither the larger
width nor a selected width schedule enters this threshold or the target.

All original guards remain: `0<w<1`, `base>0`, `base<=larger` where applicable,
`heatRatio w<=1/2`, `heatRemainderBound w<1`, and
`entropyRate 625 (adjustedCoreRate w hd)<1`. Support and time fit the named
horizon: `x.radius+1<=H` and `y.radius+lag+1<=H`. The nome, smaller source
support, horizon and lag are fixed. Physical spacing is not varied.

## Causal proof

`expectation_spatial_converges` (same module, line 411) uses the existing
`jointLimits_spatial_converge`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:85`).
Thus cutoff and exterior time are first removed in each actual width;
their already constructed joint expectations then converge spatially.
`connectedMoment_spatial_converges` (same module, line 427) combines the
three moments without replacing either mean.

`finite_connected_spatial_bound` (same module, line 440) applies
`chartScalar_spatial_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:186`)
to the joint source and both marginals. Their actual positive-action caps
give the error `B_joint + cap(left)*B_right + cap(right)*B_left`.
`connectedMoment_spatial_tail_bound` (same module, line 472) passes this
through cutoff/time removal at both widths. Then
`connectedMoment_spatial_limit_bound` (line 492) sends ONLY the later
spatial row r+d to infinity, keeping row r constant. Its bound is
`connectedAmplitude*q^(r+1-S)`, with
`q=entropyRate 625 (adjustedCoreRate w hd)` and
`S=carrierSize(boxSize base (2*H))`.

`connectedMoment_spatial_close` (line 514) uses the existing Type-valued
modulus `S+geometricCutoff(q,connectedAmplitude,epsilon)`. No modulus is
extracted from the legacy Prop-valued convergence proofs; those proofs are
used only to pass inequalities between already constructed limits.

`spatialLimit_crossOdd_pin` (line 534) uses the native center
`max(x.radius,y.radius)+1`, the existing intrinsic chart identity, and
zero-shift horizon padding. It identifies the odd bond source with
`F(x,advance 1 y)`. `spatialConnectedMoment_pin` (line 565) then retains
lag+one in the joint term and uses checked invariance of the SAME form to
identify both stationary means. `bulkConnected_pin` (line 337) connects
the estimate to the ACTUAL quotient-valued physical correlation.

Finally `rc_half_chain` (line 609) combines the existing cross-width
comparison and the new spatial comparison, each at epsilon/2. It equates
neither finite-width mean with the other. This proves the larger-width
uniformity using only the smaller-source budget.

## Verification

The final focused check on 2026-10-02 UTC exited 0 without warnings or errors:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.olean --log-file /tmp/ym-original-bulk-spatial-20261002-final.log
```

All 35 printed gates, including the 13 added declarations, lie within
{propext,Quot.sound}. No sorry, classical choice, new axiom, native proof
oracle, erased modulus or weakened frontier was added. Independent Sol
mathematical/source review passed for both the spatial join and the
larger-width consequence.

- Source SHA256: `883e391e02d488703c1bfbefbd079a4926790f03bfc2d1b14a536bc719ba5ae1`.
- Final log SHA256: `cf78231c7fb0f790567921c7b466069f4482dcfcee6507fef1361d5103a7eca7`.
- One monitored 20 GiB capped worker, 12 GiB OS reserve; no competing compiler
  or runner was found. Memory pressure reported 86 percent free before and
  after; swap remained zero. Limits were not raised.
- Existing module extended; no new root import. Full root/tree build, full
  audit, guard and progress checks were NOT run. CI remains manual-dispatch only.
- The canonical chart is unchanged: no displayed scaling or continuum claim
  closed, and no ASCII chart was reprinted.

## Remaining frontier

This supplies the scalar SAME-source spatial join for the current physical
correlations at fixed small nome. It does not justify a changing-spacing
trajectory, near-nome-one control, completed-width map or continuum OS carrier.
The complete signed energy/OWN-variance estimate on a justified changing
family remains the primary analytic input. Physical mass calibration,
nontrivial continuum survival, full SAME-theory QFT and every compact simple
group remain OPEN.
