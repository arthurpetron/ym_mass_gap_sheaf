# Original odd variance and whole-orbit generator tangent

## Result and boundary

Two actual source joins were proved after `e82e919`: a finite original odd-law
OWN variance floor at every depth, and a two-sided derivative on the entire
original signed numerical-time graph orbit. Two focused checks passed eight
permitted gates. Neither supplies a scaling-family survival floor, physical
mass calibration, continuum local fields or full QFT axioms. The whole-project
constructive Clay target remains OPEN.

## Forward: literal odd-chain nonconstancy

`lean/YMGap/Continuum/BF4DyadicWilsonSquareOddVarianceFloor.lean:55`
`originalWindowScalar_rectangular_variance_floor` applies the existing
`lean/YMGap/Continuum/BF4ExactSlabWilsonWordVariance.lean:196`
`finiteValue_variance_floor` to the actual placed dyadic selected link and
tail in the complete original ambient action. Left/right depths m,n are
arbitrary and independent of the regulator stage; the insertion is at m.

The private `odd_stage_floor` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareOddVarianceFloor.lean:79` separately
transports BOTH first and second moments through `originalWindowScalar_pin`
and `windowRatio_zero` at the SAME rectangle (depth+1,depth). Thus
`lean/YMGap/Continuum/BF4DyadicWilsonSquareOddVarianceFloor.lean:121`
`paddedSquare_oddVariance_floor` proves

    starRatio(w) <= oddVariance(original padded-square character)

for every 0<w<1, width>side(scale), K>=headCutoff(w), and depth>=0.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:87`
`oddVariance` is the actual chronological first/second-moment OWN variance,
not a substituted terminal-square law. Depth zero is included. Regulator
stage K-headCutoff(w) is constructed explicitly; no new analytic hypothesis.

The floor is width/depth/cutoff independent for fixed w. Its definition
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:46` `starRatio`
is localFloor(w)^6/localCap(w)^6, with the original computed heat floor/cap;
`:65` `starRatio_positive` proves positivity. It is NOT uniformly positive
as w approaches one, nor a continuum excitation witness.

## Rejected join: available floor plus absolute jump ceiling

The actual per-link jump ceiling already exists in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialExactKineticAlignment.lean:106`
`exact_link_displacement_nome_bound`. The ordered-word consumer is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:259`
`wilson_energy_of_link_budget`. They retain the original law, but this is an
absolute energy estimate, not a useful OWN-relative rate.

The route is ALREADY fenced by
`lean/YMGap/Continuum/BF4ExactSlabStarVarianceLossObstruction.lean:38`
`starRatio_le_defect_power` and `:78`
`starRatio_sub_mul_nome_defect_nonpositive`: the available floor is at most
(1-w)^12, and subtracting ANY C*(1-w), C>=1, is nonpositive. The new odd-law
pin does not improve that certificate number. No duplicate obstruction or
assumed-budget survival wrapper was added. This is not a statement that the
actual variance is small or actual survival fails.

## Backward: original numerical-time dynamics

`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyOrbitTangent.lean:69`
`forwardQuotientAt` and `:76` `backwardQuotientAt` define the actual quotients

    (G_(s+D)u - G_s u)/D,       (G_s u - G_(s-D)u)/D

using the SAME constructed positive-time reciprocal. The reversed backward
numerator implements division by negative time; no sign decision is made.
`:81` `forwardQuotientAt_transport` and `:88`
`backwardQuotientAt_transport` identify them exactly as G_s applied to the
existing zero-base quotients. The positive action is pinned explicitly.

The private `orbitSlope_transport` at `:94` uses the actual
`signedGraphMap_output` and signed scalar commutation. The private
`forwardOrbitError_eq` at `:111` and `backwardOrbitError_eq` at `:118` identify
the squared Hilbert-distance errors EXACTLY with their zero-base errors,
using the original signed isometry.

`:128` `PointOrbitTangent` retains radius and positivity as Type-level data.
`:144` `ofPointOrbitTangent` constructs this certificate for every supplied
original graph Point p, with radius LITERALLY
`ofPointRealTangent(hw0,hw1,p).radius`. Both errors are at most epsilon for
every signed base time s whenever the supplied positive D is within that
radius. The derivative is -2i times the output of the SAME orbit graph point.

No representatives of arbitrary quotient-domain classes are selected, no
domain-invariance axiom is supplied, and no analytic/gap premise is assumed.
The result concerns fixed nome/width and numerical time. It does not identify
physical spacing, continuum local fields, full QFT axioms or a physical
Hamiltonian mass gap.

## Remaining analytic meet

The two alternatives remain the original action-specific initial-energy
estimate consumed by
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
`completed_reference_ratio`, OR the aggregate signed-window estimate consumed
by `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`. Their useful bounds on a justified
changing family are not produced here. Preserve the COMPLETE signed
remainders, actual interacting mean and distinct original partitions.
Nontrivial continuum survival, physical calibration, full QFT structure and
every compact simple group remain OPEN; no canonical frontier atom is closed.

## Verification

Accepted focused checks (both terminal exit 0; no errors/warnings/sorryAx):

- `/tmp/ym-dyadic-odd-variance-floor-20261003-1.log`: 2 gates;
  SHA-256 `0912c2555fb39fe96a8468003c762817e579e33837829fadd59804dae791d45d`.
- `/tmp/ym-cayley-orbit-tangent-20261003-2.log`: 6 gates;
  SHA-256 `9f38610e09edcfddaaf24fd84f7e1f571a221f053d5887053edaf3f76a363124`.

Final source SHA-256 values:

- OddVarianceFloor: `f598ef34bf256f743d02c897591a3b24ea51173f565c712995a6c5042b07f424`.
- OrbitTangent: `02b454cb5fadaf79bb4a099c2c12d8ac9d4b40f1c3a1a10a4e018164f037b047`.

All eight printed dependencies are within {propext, Quot.sound}. Independent
Sol semantic reviews and Luna source/log review passed. The first failed
orbit attempt is NOT accepted
proof evidence. No new sorry, axiom, Classical shortcut, field weakening,
resource-option override or CI change. Root imports registered only; no full
root/tree build, full audit, guard or metrics run.

Checks were serialized with one compiler, 20 GiB worker ceiling and 12 GiB
OS reserve after fresh process/swap/pressure preflights. Swap was zero and
pressure-free capacity 75--76%; no limit was increased. The exact canonical
chart hash remains
`6f64d1437f38622c455b8d123f001def2a5c459eebf9e785b3e40d117b19a179`;
no unchanged ASCII chart is reprinted.
