# Exact conditional sweep and original product-energy join

Date: 2026-09-21 UTC. Status: **PROGRESS; continuum/Clay goal OPEN**.

## Mathematical result

The computed sweep integrates each selected lower link against its original
upper partner, leaving every other coordinate on the doubled carrier.
Final lower integration includes the inactive Haar projections.
`hybridMap_carrier` proves equality with the original `productMap` against
every surviving polynomial insertion. It is Haar-carrier equality, not
raw coefficient equality or merely equality of means.

The proof is finite Fubini with explicit locality: move a projection onto
its independent test, keep the current weight in that test, and recurse.
No positivity, input-degree, nome, or cutoff bound is needed for this
identity. Schedule validity and distinctness are explicit. The original
temporal geometry supplies them in the physical-slice consumer.

## Declaration map

All paths below are relative to the repository root.

| Declaration | Source | Precisely proved |
| --- | --- | --- |
| `weightedSweep` | `lean/YMGap/Continuum/SU2QuaternionWeightedProjectionSweep.lean:37` | Computed conditional-projection schedule; no unselected integration. |
| `weightedSweep_supported`, `weightedSweep_independent` | `lean/YMGap/Continuum/SU2QuaternionWeightedProjectionSweep.lean:43`, `lean/YMGap/Continuum/SU2QuaternionWeightedProjectionSweep.lean:56` | Finite support and spectator independence persist. |
| `weightedUpdate_comm` | `lean/YMGap/Continuum/SU2QuaternionWeightedProjectionSweep.lean:71` | Coefficientwise weighted-update commutation under the stated cross-independence premises. |
| `pairing` | `lean/YMGap/Continuum/SU2QuaternionWeightedProjectionSweep.lean:107` | Exact original-Haar pairing with the full signed product and independent test. |
| `heads_project_carrier` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:52` | Early lower integration preserves every surviving insertion. |
| `hybrid_updates_comm` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:77` | Distinct original lower/upper pair updates commute coefficientwise. |
| `hybridSweep_supported`, `hybridMap_supported` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:90`, `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:98` | Intermediate doubled-carrier and final one-slice support. |
| `hybridSweep_lower_independent` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:107` | A processed lower coordinate stays cleared. |
| `hybridSweep_unused_upper` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:127` | Unprocessed upper partners remain absent from the original lower-supported input. |
| `hybridSweep_pairing` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:145` | Exact full original product-heat pairing before lower drop. |
| `hybridMap_carrier`, `hybridMap_quadratic` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:163`, `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:175` | Original product-map equality with every surviving insertion, hence the same signed-input quadratic. |
| `hybridMap_square`, `hybridMap_centered_square_bound` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:185`, `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:203` | The carrier identity identifies the hybrid output square with the original product output square, then transfers the existing length-independent centered `squaredHeatRate w` bound under the explicit `headCutoff w ≤ K` guard. |
| `head_update_eq` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:217` | Literal head-chart pin to `headMap` after dropping the cleared lower coordinates. |
| `transferStep_hybrid_carrier` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHybridEnergy.lean:39` | Original interacting transfer, including V, equals the hybrid map on the original Haar carrier. |
| `energy_eq_hybrid_add_correction` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHybridEnergy.lean:49` | Original energy consumes the hybrid kinetic quadratic of V*g*f; the signed endpoint correction is unchanged. |

## Boundary and next estimate

The stronger local theorem now also has an explicit ordinary-Haar centered
square consequence for the hybrid representation. The quantitative
interacting/OS theorem remains
`headMap_defect_le_angular` at
`lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:271`.
The new identities do not themselves telescope its bound over changing
hybrid inputs. They do not remove the inactive Haar projections, which
are explicitly part of `hybridMap` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:68`.
A singleton `productMap` is NOT identified with `headMap`.

The original signed correction remains the `correction` defined at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:60`.
The existing differential cancellation is
`endpoint_angular_cancellation` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:173`;
it is not a finite-time cancellation for P. The guarded active-carrier
energy reduction is `energy_active` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`.

Quantitative tensorization, interacting finite-time comparison, SAME-variance
small rate, spatial/scaling survival, finite physical mass, canonical full
QFT and every compact simple group remain open. No canonical field was
weakened and no hole or axiom was introduced or discharged.

## Verification and independent review

Sol supplied the bounded generic sweep algebra. Main implemented the actual
product/energy joins and ran all verification serially. Sol's independent
read-only scope review passed: spectators, inactive links, operator identity
strength and the signed correction are represented faithfully.

Three focused checks for the original sweep/energy milestone passed **16
printed gates**. A follow-up focused check for the two new square-norm
theorems passed **12 printed declarations** (10 repeated plus the 2 new
theorems). All were within
`{propext, Quot.sound}`. The dependency-complete target
`+YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy:olean` also passed.
One capped 20 GiB worker, 12 GiB reserve and monitored swap limits were used.
No full-root build, full-tree audit or frontier guard was run. Root imports
were added; this does not imply full-root verification.

| Focused log | SHA-256 |
| --- | --- |
| `/tmp/ym-gap-weighted-projection-sweep-check.log` | `546005d1822cae9fb95d328150be89fbaf082ebdbdecbd8bf0c1967d0e6dfaa8` |
| `/tmp/ym-gap-product-heat-hybrid-sweep-check.log` | `9a0e651be286548e98a02786f0691a4c62754710fd4955f560078ad1fddcc419` |
| `/tmp/ym-gap-fixed-spatial-hybrid-energy-check.log` | `300c77f6872ac887423708c19d24e1691fdda2f0545e69e28f0fceeae3cce2c1` |
| `/tmp/ym_hybrid_square_check3.log` | `7313ab4677d4c2a427d6f9bd0def065605e1d0d720744bd38741f6036fa0fef3` |

The final target log `/tmp/ym-gap-fixed-spatial-hybrid-energy-build.log`
is empty under the quiet launcher; its monitored command completed with
exit status 0. The focused logs above contain the axiom evidence.
