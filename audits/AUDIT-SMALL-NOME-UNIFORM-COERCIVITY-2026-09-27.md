# Audit: small-nome uniform coercivity (2026-09-27)

## Result and scope

The new theorem `BF4ExactSlabSmallNomeUniformCoercivity.volume_uniform_centered_coercivity` proves, on the original completed full-action GNS carrier, that

`coefficient hd * normSq x ≤ finalEnergy (schedule extent) x`

for every centered completed vector `x`, every extent, and every cutoff `K = headCutoff w + stage` (source: `lean/YMGap/Continuum/BF4ExactSlabSmallNomeUniformCoercivity.lean:62`). The scalar is `coefficient hd = half * gamma`, with `gamma = 1 - 50 * e` and `e = (U-L)/(2L)` from the pair comparison (`BF4ExactSlabSmallNomeUniformCoercivity.lean:41`; `BF4ExactSlabConditionalGeneratorMargin.lean:23`; `BF4ExactSlabTwoLinkResidualLowerBound.lean:44-47`). Thus the final coercivity coefficient is `b = gamma/2`. The norm and energy are the original unnormalized forms; no normalized-vector premise is introduced.

At the exact pilot nome `w=1/1024`, `existingNome_centered_coercivity` proves positivity and the same estimate without leaving scalar smallness or analytic coercivity as assumptions (`BF4ExactSlabSmallNomeUniformCoercivity.lean:89`; `BF4ExactSlabConditionalGeneratorMargin.lean:40`). The proof discharges the guards `0<w<1`, `heatRatio w ≤ half`, `delta<1`, and `gamma>0`; the existing pilot guards are in `BF4ExactSlabSmallNomeHaarComparison.existingNome_guards` (line 195), while the margin positivity is the exact rational proof `existingNome_margin_positive`. All module paths abbreviated in this report are under `lean/YMGap/Continuum/`.

## Mechanism and limits

The residual-generator square bound has ordered signed-neighbor multiplicity `2*25=50` and yields the margin `gamma=1-50e` (`BF4ExactSlabConditionalGeneratorLowerBound.lean:71,94`; its endpoint incidence bounds are each 25). No spectral theorem is used. The iteration step is `1/(2*(numberLinks+1))`; its rate `q=1-step*gamma` depends on `schedule extent` (`GNSResidualGeneratorStepSize.lean:19`; `BF4ExactSlabConditionalGeneratorDecay.lean:34-38`). This volume-dependent `q` is only an internal convergence rate, not the volume-uniform coefficient `b` or a physical mass rate.

For centered inputs, the iteration preserves centering (`BF4ExactSlabConditionalGeneratorIteration.lean:71,92`). A positive finite-volume baseline is used only to bound and remove the vanishing norm tail; `RCDescentCoercivity.descent_coercivity` explicitly leaves the final coefficient independent of that baseline (`RCDescentCoercivity.lean:61-68`). The geometric-error closure eliminates a representative bound propositionally and explicitly does not assign a Type-valued convergence modulus to arbitrary `RC` classes (`RCGeometricErrorClosure.lean:1-5,20`). This adds no quotient-modulus claim.

`volume_uniform_reverse_energy` then feeds the centered estimate at the balanced output into the existing reverse-energy consumer (`BF4ExactSlabSmallNomeUniformCoercivity.lean:106`); `reverse_coefficient_gt_two` records strictness (`:118`). This is still ordinary original-action conditional-link dynamics, not OS translation, a continuum scaling family, or a physical Hamiltonian gap. The next required consumer is the original Chebyshev covariance argument using the support- and degree-independent reverse coefficient. Physical scaling, OS/QFT identification, nontrivial continuum survival, and a mass gap for every group remain open. No chart/status change is implied.

## Focused check record

The checked set comprises exactly these 11 new targets and 47 printed gates (tracked dependencies are not counted):

| New target | Gates |
|---|---:|
| `BF4ExactSlabConditionalGeneratorDecay` | 5 |
| `BF4ExactSlabConditionalGeneratorIteration` | 5 |
| `BF4ExactSlabConditionalGeneratorLowerBound` | 3 |
| `BF4ExactSlabConditionalGeneratorMargin` | 3 |
| `BF4ExactSlabSmallNomeUniformCoercivity` | 6 |
| `GNSProjectionNeighborLowerBound` | 1 |
| `GNSResidualGeneratorDescent` | 4 |
| `GNSResidualGeneratorStep` | 13 |
| `GNSResidualGeneratorStepSize` | 5 |
| `RCDescentCoercivity` | 1 |
| `RCGeometricErrorClosure` | 1 |
| **Total** | **47** |

Each passed a focused serialized check through `scripts/safe_lean_build.py`
with `--jobs 1 --check-worker-limit-gib 20 --check <source>` and its matching
`--check-output` olean. All 47 reported axiom sets are contained in
`{propext, Quot.sound}`; none contains `sorryAx`. This is not a full repository
or root-module build, full audit, guard, progress-metric, or CI run.

Independent Sol review confirmed the two-endpoint count, the SAME original
constant/carrier throughout the iteration, cancellation of the old baseline
from the endpoint coefficient, and the stated fixed-nome parameter scope.
No new hole, analytic bundle, or weakened frontier field is introduced.
