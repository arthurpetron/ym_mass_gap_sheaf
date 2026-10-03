# Repointed frontier: retain the combined ORIGINAL signed cost

The whole-project target is unchanged: nontrivial continuum Yang--Mills on
R^4 for every compact simple group, SAME-theory QFT axioms and a finite
positive physical mass gap. It remains OPEN. The SAME-carrier root/log
identification is checked; it supplies no changing-family analytic estimate.

This note isolates a proof TARGET from existing exact identities. The target
inequality below is NOT a theorem, certificate, or estimate proved here.

## Keep the actual source and both partitions

For the original padded square of side s, put h=1-w and let c_n be its
actual OWN mean. Keep psi_n=f-c_n and the literal blocked source

    A=g_(n+t), b=T^t(g_n*psi_n),
    Z0=ell(A^2), Z1=ell(A*T A).

Do not recenter b at n+t. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244`,
`original_block_rayleigh_split`, proves the raw exact split

    D=Z0*energy(A,psi_n)+boundary+signedMultiplicationCost(A,b,psi_n).

`BF4ExactSlabFixedSpatialFamilyBandResponse.lean:130`, `energy_shifted`,
removes a constant shift from the energy, not from the blocked source.
`BF4DyadicWilsonSquareVarianceTaylor.lean:257`,
`paddedSquare_energy_variance`, pins the ORIGINAL normalized energy to

    12*s*h*V_(n+t)+R_(n+t),

where V is SAME original odd variance. `BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:49`,
`varianceRemainder_raw`, retains

    R=(signedRemainder-h*wardResidual)/Z1.

`BF4DyadicWilsonSquareWardMoments.lean:413`, `paddedSquare_varianceRemainder`,
expresses its Ward correction by the actual interacting character moments.
`BF4ExactSlabFixedSpatialSignedMultiplicationWindow.lean:72`,
`normalizedSignedMultiplicationCost`, retains BOTH partitions in M.
All source paths in this section have prefix `lean/YMGap/Continuum/`.

## Minimal cancellation-preserving producer target

The exact normalized split has the combined signed expression

    D/(Z0*Z1) = 12*s*h*V_(n+t) + R_(n+t) + M_(n,t)
                + boundary/(Z0*Z1).

For the desired finite relative block cost, the useful unpaid target is

    s*(R_(n+t)+M_(n,t))
      <= C*ell(b^2)/Z0 - 12*s^2*h*V_(n+t),

with a computed allowance for the already controlled finite boundary and
limit errors. This is a producer obligation, NOT an input to a new wrapper.
It must hold on a JUSTIFIED changing family, with useful uniform C and
original cutoff/depth onsets. Separate absolute values erase its cancellation.

`BF4WilsonAllNomeSignedMultiplicationLimit.lean:117`,
`signedCostLimit_completed_pin`, and :132, `signedCostLimit_nonpositive`,
prove at fixed parameters M tends to delta_(2t)-delta_0<=0. Its sign alone
gives delta_(2t)<=delta_0, not a useful relative size against the filtered
response C_(2t). An alternative initial-energy/retention comparison
s*delta_0<=C*C_(2t) is still unpaid; replacing M by zero does not produce it.

The stronger existing energy ceiling in
`BF4DyadicWilsonSquareSobolevProjection.lean:246`,
`paddedSquare_energy_sobolev_projection_bound`, retains
completeSobolevCenteredDebt - half*h^2*normalizedProjectionGain.
Those signs and the Ward correction should remain inside the combined cost;
their useful relative changing-family estimate is NOT supplied here.

## Match the consumer's actual lag

`BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136`,
`originalOwnBlockVariance_converges`, and :157,
`originalOwnBlockCost_converges`, pin the finite denominator/cost to SAME
norm times response C_(2t) and SAME norm times delta_(2t).
The output is a SHIFTED filtered budget. It is not automatically the raw
start-one hypothesis `hbudget` or reserve `hreserve` in
`BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`,
`dyadicUnitResponse_filtered_block_floor`.

The next work must preserve this lag and show the SAME family/normalization
meets the existing backward consumer. No fresh conditional recoding closes
that gap. Canonical OS realization, nontrivial continuum survival, physical
calibration, full QFT and every-group construction remain OPEN.

Independent Sol review identified this residual; root inspected the cited
source declarations. This is source-backed proof planning, not new kernel
verification or a new analytic theorem.
