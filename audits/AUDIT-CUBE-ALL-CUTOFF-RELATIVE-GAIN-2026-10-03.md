# Original cutoff-uniform relative signed gain on the finite cube

The continuum Yang--Mills/Clay target remains OPEN. This increment removes
the cutoff-one restriction from the original finite signed-gain pilot. It
does not remove the fixed coupling, width two, or terminal-depth-zero
restrictions, and is not completed-state or continuum survival.

## Proposition and causal argument

Keep the ORIGINAL transfer T_K, full weighted functional ell_K, and bent
six-link fundamental trace F. Fix w=1/16. For every K satisfying BOTH
1<=K and headCutoff(w)<=K, let

    c_K = existing original odd-law mean at depth zero,
    U_K = T_K 1,
    b_K = T_K F - c_K U_K,
    S_K = ell_K[b_K^2],
    Q_K = ell_K[(U_K(F-c_K))^2],
    a   = w^18,
    G_K = existing commutatorGain(w,K,2,0,F,c_K,a).

The checked result is the actual relative signed inequality G_K>=S_K/4, together
with a computed positive floor. No interacting eigenvalue is assigned to F.

The short mathematical step is to move the first-face trace P through the
original kinetic map BEFORE estimating its action tail. P has the EXACT
kinetic multiplier w^12 at EVERY K>=1. Thus

    H[P b_K] = w^12 H[P(F-c_K) Vcube_K].

The already checked cutoff-one action channel is

    alpha/2 + alpha^5/8 - c_K(alpha + alpha^5/16),
    alpha=coeffW(w,1)=2^-11.

For any |c_K|<=1/4 this is >=alpha/4. The actual high-label heat tail
starts at label two and has a constructed interval cap 2^-20. Telescoping
all six shared face factors gives the actual action difference
Vcube_K-Vcube_1 cap 2^-17. With BOTH test caps |P|<=2 and |F|<=2 retained,
the action-channel error is <=(9/2)*2^-17 < alpha/8. Its exact kinetic
multiplier is still outside the error. Consequently

    H[P b_K] >= z = w^12 alpha/8 = 2^-62,
    S_K >= (1/2) z^2 = 2^-125.

The same action has a constructed half-floor, used after the original
fringe/action transport. The literal original U_K has a cutoff-uniform
remainder interval <=1/32. Together with Vcube_K-1<=1/32 this constructs
the OWN odd background band 65/1024. Its actual original odd partition
is >=959/1024 and bent numerator has absolute value <=130/1024. Division
by that SAME partition proves |c_K|<=1/4; bare Haar centering is not used.

The full original Young cost retains Vcube_K, U_K^2 and (F-c_K)^2, and
is <=128. The exact original Young square therefore gives

    2 G_K >= S_K - a^2 Q_K,
    a^2 Q_K <= 2^-137 <= S_K/2,
    G_K >= S_K/4 >= 2^-127 > 0.

The explicit cutoff family max(1,headCutoff(w))+extra inhabits both guards.
Uniformity is in finite K only; nome, width and terminal depth are fixed.

## Source anchors

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffInterval.lean:120`,
  `heatTailInterval`; :216, `cubeRemainderInterval`; :257,
  `cubeDifferenceInterval`; :285, `cubeHalfCertificate`; :303,
  `cubeCertificate`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer.lean:93`,
  `tested_bent_transfer_pin`; :111, `tested_centered_channel`; :168,
  `tested_centered_cutoff_decomposition`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffGainTransport.lean:78`,
  `original_commutator_gain_pin`; :172, `centeredSquare_cube_pin`; :181,
  `youngCost_cube_pin`; :221, `gain_young_lower`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffVacuumInterval.lean:111`,
  `cubeVacuumInterval`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffChannelFloor.lean:109`,
  `testedActionRemainder_abs_le`; :143, `tested_centered_channel_lower`;
  :203, `centeredSquare_channel_lower`.

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffOwnMean.lean:190`,
  `oddPartition_floor`; :207, `oddNumerator_abs_le`; :255,
  `originalOddMean`; :288, `originalOddMean_abs_le`; :292,
  `existingMean_abs_le`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffOwnGain.lean:76`,
  `centeredYoungCost_le_128`; :92, `centeredGain_relative_lower`; :135,
  `originalOwnGain_relative_lower`; :144, `originalOwnGain_floor`; :152,
  `originalOwnGain_positive`; :162, `guarded_originalOwnGain_positive`.

## Accepted verification boundary

Seven final serialized focused checks exited zero with **49 distinct printed
gates**, all within {propext, Quot.sound}; `finiteGainFloor_positive` has no
axiom dependencies. No accepted log contains errors, warnings or `sorryAx`.
Failed development logs are not accepted evidence. Each check used
`scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 --check-worker-limit-gib 20`
with an explicit target and output. Dynamic capacity was checked before
every launch; the final launches had 86% system-wide free memory, zero swap
and no competing Lean jobs. No worker/resource limit was raised.

The source basename prefix below is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoff`.
The accepted log prefix is `/tmp/ym-cube-all-cutoff-`, with suffix
`-20261003-<version>.log`. Hashes are SHA-256 of the exact checked sources
and accepted logs.

| Source suffix | Accepted log suffix/version | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `Interval.lean` | `interval` / `c` | 6 | `bc64f4d54381280b58e1400887f8b03bd03d3043ff2bc7d3fd1c73517efaa906` | `6a869526504280ea718cb55e2f66457e12aa1ee8899243c9d2ee284ba745b10d` |
| `TestedTransfer.lean` | `testedtransfer` / `a` | 5 | `68149a3445da1c2ba1a71a425a459cd81ab64c8653503eef68ad788d3e80ad71` | `b29ebfdea683c0a82e83d1cf30b423f43970a42f96a188aabc708f763b521987` |
| `GainTransport.lean` | `gaintransport` / `a` | 10 | `a3bd9f477fd2fce54b85de100dbfc3b26541059a6dba38f46f9f1d1be070dac8` | `18edefbb2b4a3c35ecb533bd7a4651ee89262ffa2b967beb1578f0485107dab3` |
| `VacuumInterval.lean` | `vacuuminterval` / `a` | 2 | `76b95a6006e0c8218d55ff7a3e4d18871da6b9e8a8f4ce7f0bba56ba3e7e6ab0` | `a83da2d8e1884b85c3605cb7781c9ae9ac8073a1eeb3b788ffced31074a8f96b` |
| `ChannelFloor.lean` | `channelfloor` / `a` | 4 | `c7f6eba143d2defc470b781cdf4742fb2559bdc9d04dc078cb16dfeda3046b8b` | `dfe956d5de1b035c5fed172c960ddc5985ac610cd178f2f9349c767e9722058d` |
| `OwnMean.lean` | `ownmean` / `d` | 15 | `c02418fd3c89e38431afeaf369bdaef323a12628ef64c38232dcf82bb7453c4f` | `f66cf9b13346b135e6fc2bbdaba223aeccec4fb923efc5a33609ff9618f1371c` |
| `OwnGain.lean` | `owngain` / `b` | 7 | `c4c91ab7a570f4b798e90ad44cc34c13a78256b45aa2b732bd2c92ec44ca8ba7` | `7cc92d7aeeacb5ffe90697e2ac903a85514d3e135235639ce7871c1ba6e4327e` |

Root imports are registered only; the aggregate root, broad audit/guard and
progress metric were NOT run. CI remains off. The canonical first fenced
chart is unchanged, SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed claim closed, so no ASCII chart is reprinted.

Independent read-only final reviews passed: Sol checked the mathematical
argument, original-object pins, both guards and scope; Luna checked all
seven source/log hash pairs, 49 outputs, declaration anchors, documentation,
root-import registration and unchanged chart. Neither reviewer ran builds.

## Forward/backward boundary

FORWARD: this supplies a genuine original finite signed producer, now with
unbounded guarded cutoff and a SAME-filtered-square relative lower bound.
It is not just an implication assuming a favorable gain.

BACKWARD: the current completed survival consumer still needs the SAME
macroscopic response ratio on a justified changing family, or a sufficient
signed block-Rayleigh estimate. This depth-zero, fixed-small-nome cube
result is not that family input. Terminal-depth control, growing-loop and
spatial comparison, changing coupling/spacing, completed survival, physical
mass calibration, full SAME QFT and every compact simple group remain open.

The useful method carried forward is the exact tested-transfer identity:
preserve its kinetic factor before bounding action remainders. Next seek
the corresponding cancellation/control with the original terminal source
V*g_n; do not infer a late-depth floor from this depth-zero result.

The independent next-frontier source review identifies the exact general
tested identity `H[P*b_n]=w^12*ell[g_n*P*(F-c_n)]` from
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:48`,
`transferStep_eq_productMap`;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:72`,
`kineticMap_symmetric`; and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteKinetic.lean:69`,
`plaquette_kinetic_eigen`. This is a source-level composition review,
not an additional checked declaration. The actual positive amplitude
mu_n=ell[g_n] is supplied by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:131`,
`terminalMessage_mass_positive`. The quantitative projection signal
ell[g_n*P*(F-c_n)]/mu_n and endpoint cost
ell[g_(n+1)^2*(F-c_n)^2]/mu_n^2 remain unpaid. The OWN c_n uses the
distinct odd law V*g_n*g_(n+1); it cannot be replaced by the one-terminal
law. Neither comparison follows from terminal positivity or this n=0 floor.

Source review also confirmed that the integrated diagonal Hessian sign
alone supplies no sign for the actual unequal-endpoint vacuum-subtracted
cost: `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:144`,
`productHeat_upperHessian_eq_neg_square`, has matching endpoints, whereas
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainStein.lean:141`,
`paddedSquare_commutatorGain_source_gradient`, retains unequal signed
source/test factors. This is a source review, not a new refutation theorem.
