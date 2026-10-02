# Original family-band coefficient: checked calibration obstruction

## Outcome and actual consumer

The existing original padded signed-family bound DOES exist:
`BF4WilsonAllNomePlaquetteFamilyBondFloor.finite_family_energy_band`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondFloor.lean:165`)
proves E <= (1-rho)*OWNVar at every positive depth and late heat cutoff.
The original action, source, own mean and partition are preserved.

For every strict rational nome and nonempty family, THIS explicit coefficient
satisfies rho <= (1/32)^(56*size) <= 2^(-280), hence 1-rho >= 1-2^(-280).
Original completed reference transport multiplies it by (1+comparisonEta)^2
>=1, so no width, nome or reference depth turns it into a small coefficient.
This bounds a computed UPPER-BOUND COEFFICIENT, NOT the true E/OWNVar ratio.
It does not reject a stronger signed estimate or supply a Yang--Mills counterexample.

## Original inputs and short argument

- `BF4ExactSlabFixedSpatialFamilyBandResponse.familyResponseFraction`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:165`)
  is w^12*l*l/(u*u), with l=localLower(w,4*size), u=localUpper(w,4*size).
- `BF4ExactSlabFixedSpatialUniformLocalBand.localLower` and `localUpper`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`,
  same module line 47) give l=headFloor^(28*size), u=prefixCap^(28*size).
- `BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond`
  (`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`) and
  `BF4ExactSlabStarRateObstruction.prefixCap_ge_one`
  (`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`) give
  headFloor<=1/32 and u>=1. The original floor remains strictly positive.
- `HeatKernelGap.qpow_le_one`
  (`lean/YMGap/Continuum/HeatKernelGap.lean:99`) gives w^12<=1.

Drop only nonnegative factors bounded above by one; compare the floor powers
with (1/32)^(28*size) and combine the exponents. Exponent antitonicity gives
the nonempty-family bound. No schedule or asymptotic inference is needed.

`BF4WilsonAllNomeTerminalReferenceEnergyRatio.referenceCoefficient`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:42`)
is c*(1+eta)^2. The existing `comparisonEta_nonnegative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:97`)
gives referenceCoefficient>=c when c>=0. This is the actual coefficient in
`completed_reference_ratio`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`).

## New checked declarations

| Declaration | Module:line | Scope |
| --- | --- | --- |
| `fractionCeiling` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:41` | Explicit size-dependent rational ceiling. |
| `coefficientFloor` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:45` | Barrier 1-(1/32)^56. |
| `familyResponseFraction_le_ceiling` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:64` | Every strict nome and list size. |
| `fractionCeiling_nonempty` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:101` | Every positive list size. |
| `coefficientFloor_ge_half` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:107` | Arithmetic barrier, without a huge closed-power evaluation. |
| `family_band_coefficient_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:117` | Existing band coefficient, not actual energy. |
| `referenceCoefficient_ge_input` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:124` | Original transport cannot decrease a nonnegative coefficient. |
| `transported_family_band_coefficient_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:139` | Every width and reference depth. |
| `transported_family_band_linear_budget_false` | `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:151` | Cannot pay C*a<1/2; no physical meaning of a is assumed. |

## Verification

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.olean --log-file /tmp/ym-family-band-calibration-20261002-final.log
```

Exit 0. Seven public printed gates, all {propext,Quot.sound}; no error,
warning or sorryAx in the final log. The first draft log failed elaboration
and is NOT evidence. Arithmetic power comparison replaced a needlessly deep
closed-rational computation; no resource limit rose. Pre/post checks reported
86% memory-pressure free and zero swap; no compiler/runner was present before
or survived after. One 20-GiB worker and the 12-GiB reserve were unchanged.
Sol independently reviewed the mathematics and scope: PASS. Luna independently
located the original constant definitions and bound inputs, then checked the
final hashes, all seven gates, citations, documentation scope and unchanged
ASCII block: PASS. No new sorry,
axiom, classical/native oracle, analytic premise, erased witness or weakened
frontier was introduced.

| Artifact | SHA-256 |
| --- | --- |
| `BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean` | `b1c6ba3c89e7f55f91ff274597f828e01b7b19f634db5c124d44800dcd156197` |
| `/tmp/ym-family-band-calibration-20261002-final.log` | `a9ad98a1fddc505f5a1831fdf0d82ce374de10f7d45b68c1ef1e818721e149e1` |

## Repointed frontier and residue

Do not calibrate THIS positive response-band constant as a spacing-small
upper-energy producer. Preserve its genuine fixed-nome nontriviality results.
The true ratio can be much smaller: this proof does not reject a smaller
coefficient supported by an actual finite margin.

NEXT: useful actual original signed-margin data or joint signed Taylor/source/
Ward cancellation on a justified padded/changing family, not an isolated
score envelope or this absolute window band. The finite margin criterion
and original cutoff/depth/limit transport remain the consumers. No accepted
small-rate data were produced. Cross-scale pairings, spatial/spacing control,
nonzero continuum survival, finite positive physical mass, full same-theory
QFT, every compact simple group and Clay remain OPEN. One semantic root import
added; full root/tree build, axiom audit, guard and progress-metric script NOT
run. CI and exact canonical chart claims unchanged; no ASCII reprint.
