# Exact heat defect in the original half-smoothed determinant

The unchanged whole-project continuum Yang--Mills/physical mass-gap target
for every compact simple group remains OPEN. This increment is an exact
finite SU(2) identity, not a useful uniform inequality or continuum result.

## Proved identity and literal consumer

Use the ORIGINAL transfer, terminal messages and weighted mass ell. Put

    f = original padded-square fundamental trace,
    c_n = middleRatio(n+1,n,f), psi_n = f-c_n,
    A = g_(n+t), b = T^t(g_n*psi_n),
    Z0 = ell(A*A), Z1 = ell(A*T A),
    a = w^(12*side(scale)),
    v = OWN odd variance at depth n+t,
    M = squareSignedHeatDefect at depth n+t.

The now checked identity is

    D = Z1*ell(b*b) - Z0*ell(b*T b)
      = Z0*((1-a)*Z1*v-M)
        + boundaryDrift(A,psi_n)
        + signedMultiplicationCost(A,b,psi_n).

`paddedSquare_exact_block_heatDefect` is at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareExactBlockHeatDefect.lean:65`.
It names 0<w<1, headCutoff(w)<=K, n, t, scale and side(scale)<width.
There is no additional K>=1/K>=2, stationarity, sign or reserve premise.
No Taylor/cubic/omitted-mode estimate is used.

Under K=headCutoff(w)+stage and n=stage, the literal source, chronological
center and partitions match `originalOwnBlockCost` and
`originalOwnBlockVariance` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98`
and `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`.
Their SAME completed limits are `originalOwnBlockCost_converges` and
`originalOwnBlockVariance_converges` in that file at lines 157 and 136.
No new state, partition or limiting observable is introduced.

## Causal proof joins

- `original_block_rayleigh_split`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244` retains the entire signed multiplication cost.
- `iterateStep_add`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:47` pins the actual blocked terminal to g_(n+t).
- `energy_shifted`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:130` removes c_n ONLY inside the shift-invariant energy.
- `paddedSquare_energy_signedHeatDefect_identity`, `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:129` gives the exact energy at depth n+t.
- `terminalMessage_next`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:57` pins its odd partition to Z1, not Z0.

## Verification boundary

One serialized focused target passed using the monitored launcher, one
worker, 20 GiB cap and 12 GiB OS reserve. Preflight: 84% memory free, zero
swap and no competing compiler. The accepted log has one gate, exactly
{propext, Quot.sound}, and no error, warning, sorryAx or PANIC.

Accepted log: `/tmp/ym-square-exact-block-heat-defect-20261003-c.log`.
Source SHA256: `e75a16255adc4db99a5cd3852c2daf0df57cf51933f50b50b42289249c965864`.
Log SHA256: `e1abe93c794464788101601d423e4d492d8bec0c5774d0ce858a6ce253a6e078`.
Initial attempts exposed a missing namespace and excessive definition
unfolding; explicit local composition fixed these without increasing
heartbeats, changing resources or weakening the statement.
No full-root/tree build, broad audit/guard or progress metric ran.
Root import is registration-only; no sorry added/discharged, no new axiom,
frontier weakening, CI change or exact displayed chart change.

## The quantitative producer remains unpaid

For even dyadic side s and t=s/2, the needed bound is

    s*[Z0*((1-a)*Z1*v-M) + drift + signed multiplication cost]
      <= C*Z1*ell(b*b),

with the actual changing-family control and limit allowances. Equivalently,
the original determinant budget must retain the vacuum scalar:
s*Z0*ell(b*T b)>=(s-C)*Z1*ell(b*b).
No replacement of the filtered norm ell(b*b)/Z0 by v, favorable sign of M,
or relative control of the signed multiplication cost is proved here.
Canonical OS, spatial/spacing control, nontrivial continuum survival,
physical calibration, QFT, every group and Clay remain OPEN.
