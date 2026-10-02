# Finite scalar sampling for original anchored Wilson responses

## Result and scope

The new checked theorem reduces comparison of the original anchored
integer-time response to finite one-dimensional scalar tables. A table error
eta gives error eta+2^(-p-1) for all covered matching cells, even at different
nomes and widths. The theorem does NOT supply those cross-scale table
estimates, a surviving anchor norm, a changing-family limit or a mass gap.

All new declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseSampling.lean`.

## Exact inputs and reduction

`sampleLag` (line 35) is 2*side(scale)+v*2^(scale-p).
`sampleResponse` (line 38) is the existing `dyadicUnitResponse`, with the
same constructed norm-one centered Wilson square and original transfer.
`sample_spacing_pin` (line 58) proves its increment has assigned geometric
time v*half^p when p<=scale. The full response lag includes anchor time 2;
this arithmetic is not physical Yang--Mills time calibration.

`dyadicUnitResponse_cell_bounds` (line 88) proves

    R(sampleLag+i) <= sampleResponse <= R(sampleLag+i)+half^(p+1)

for i<2^(scale-p), including v=0 and i=0. The response shift bound uses
1/(sampleLag+1)<=spacing(scale+1), since sampleLag>=2*side(scale).
Nome, width, cutoff and terminal depth do not enter this cell-error constant.
The underlying same-state theorem is `dyadicUnitResponse_shift_bounds`
at `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean:121`.

`sample_cell_compare` (line 123) consumes both-order eta comparison at ONE
sample v. Monotonicity pays only the receiving family's cell error in each
direction, yielding eta+half^(p+1), not two cell errors.
`sample_table_compare` (line 147) uses natural quotient and remainder to
cover all integer queries whose cell indices agree and are less than count.
Strict nome and padding guards remain explicit for each original family;
no map between its completed carriers is used.

`finiteSampleModulus` (line 177) RETURNS the finite maximum of supplied
sample moduli. `finiteSampleModulus_spec` (line 188) bounds every entry by
that maximum. `sample_table_tail_compare` (line 196) actually consumes those
per-sample tail comparisons for nome(k),width(k), at the computed cutoff
max(p,finiteSampleModulus). Its input comparisons explicitly require k,l>=p.
No per-sample comparison or modulus is manufactured by the theorem.

The original bond Gram pin is `anchoredBond_pairing` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchor.lean:106`:
the entry at i,j is R(2*side+i+j). Thus the new table theorem can compare
integer-grid Gram entries by their sum-time cell. A common continuum carrier,
all-real cross-scale comparison and the full Schwinger functional are not
constructed here.

## Forward estimate still missing

The parallel forward review reconfirmed EXISTING `wilson_energy_nome_bound`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyKineticUpper.lean:101`.
For the padded square it gives E/Z<=192*(1-w)*side^2, retaining the complete
terminal source and without source derivatives or a volume coefficient.
It is an absolute bound, not an OWN-variance-relative survival estimate.
The coarse starRatio join is already excluded by
`no_starRatio_rational_loss_budget` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:117`.
Neither existing result is counted as new progress in this increment.

The exact retained-curvature criterion remains
`dyadicUnit_response_lower_iff` at
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:210`:
survival at 2*side requires useful control of 2*side*loss-C_(2*side).
Actual signed/radial comparison with OWN variance and actual cross-scale
sample drift remain unsupplied on a justified changing family. The Clay
target, physical calibration, full SAME-theory QFT and every group remain OPEN.

## Verification

The accepted focused check exited 0 without errors or warnings:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseSampling.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseSampling.olean --log-file /tmp/ym-dyadic-response-sampling-20261002-second.log
```

All nine printed gates are within {propext,Quot.sound}; sampleLag and the
finite modulus are axiom-free. The first check failed on an underspecified
finite-fold function argument and is NOT accepted proof evidence. That
argument was made explicit. Independent mathematical review also removed
unnecessary sample premises below p. No sorry, axiom, resource limit increase
or canonical frontier-field change was introduced.

Source SHA256: `584e714f220b6cc2d47486656351b14ff4f1c297f5e3694369f8a7a0f72774e3`.
Accepted log SHA256: `43085966d2e39b29bce3780a9c4ad607f106b727b8987aa7e4294313bb097be8`.

One monitored 20 GiB-capped worker retained the 12 GiB OS reserve; preflight
reported 84--85 percent pressure-free memory and zero swap, with no competing
compiler or runner. One root import was registered. Full root/tree, broad
audit/guard and progress metric were NOT run. CI and the exact canonical
chart block are unchanged; no paper-list or unchanged chart reprint.
