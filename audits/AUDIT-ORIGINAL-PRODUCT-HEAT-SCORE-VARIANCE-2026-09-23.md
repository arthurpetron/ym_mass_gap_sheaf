# Whole original product heat: coefficient-square score and SAME variance

Date: 2026-09-23. Scope: finite constructive SU(2) polynomial Haar estimates.
The continuum Yang--Mills/Clay target remains OPEN.

## Actual new conclusion

Let W be the actual selected product `productHeat n w K ids`, let
R=a(x)*a(y), Z=H[R W]>0 and r=1/Z. Let D be the whole signed upper angular
direction represented by `terms`, with coefficient c_t and block b_t. Define

```
L_i = sum_{t : b_t=i} |c_t|
S   = sum_{i in ids} sum_{t : b_t=i} c_t^2
Lambda = sum_{i in ids} L_i*(L_i*C(w)).
```

Every occurrence in both lists is retained. The checked theorems give

```
(r*H[R*(D W)*f])^2 <= Lambda * r*H[R W f^2]
Lambda <= m*C(w)*S                 if every selected local term count <= m
(r*H[R*(D W)*f])^2 <= m*C(w)*S*Var_RW(f).
```

The last variance is the existing `QuaternionHaarDensityVariance.normalizedVariance`
of the SAME weight R*W, with the SAME positive mass Z, not a new measure or
an OS-norm surrogate. Source a has a `Certificate n a` and support in n
blocks; f is an arbitrary signed polynomial supported in 2n blocks. The
normalized statements keep the explicit hypothesis Z>0. They do not invent
a normalized zero-source law; the homogeneous product bound also covers it.

## Mathematical proof

1. Derivatives at an unselected upper block annihilate each relative heat
   factor. The first local derivative remains independent of the other upper
   blocks, so the SECOND derivative also localizes. Both statements concern
   the actual heat, not a supplied locality hypothesis.
2. Sum the constructed mixed log-curvature entries with their signed
   coefficients. Each factor costs C(w)*L_i^2; exact product-curvature
   composition adds these local costs and retains all mixed terms.
3. Multiply the certified positive heat floors. The resulting finite floor
   is `headFloor(w)^ids.length`. Use it only in the constructive integrated
   positive-factor cancellation theorem. The floor and polynomial upper cap
   add no new factor to the final Lambda. C(w) itself still has floor dependence.
4. Apply the existing whole-product integrated Hessian sign and dual square
   completion. Normalize by the actual positive Z on both sides.
5. Finite rational Cauchy gives L_i^2 <= localCount_i*sum_local c_t^2.
   Summing gives the stated m*C(w)*S with a LOCAL multiplicity bound.
6. Kinetic symmetry and signed Haar integration by parts give
   H[R*(D W)]=0: the source pairing B(Da,a) is both equal to B(a,Da)
   and its negative. This identity needs no positivity or late-cutoff guard.
   Subtracting any scalar from f therefore leaves its score unchanged.
7. Apply the bound to the existing polynomial center at the SAME normalized
   mean. Its checked norm identity is exactly the original normalized variance.

## Load-bearing declaration map

Paths below are relative to the repository root.

| Declaration | Source |
| --- | --- |
| `heatAt_upperDirection_second_localize` | `lean/YMGap/Continuum/SU2QuaternionSignedAngularLocality.lean:155` |
| `heatAt_localSignedCurvature` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSignedLogCurvature.lean:54` |
| `productHeat_signedCurvature` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSignedLogCurvature.lean:106` |
| `productHeat_floorCertificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatPositiveFloor.lean:67` |
| `productHeat_dual_score_bound` | `lean/YMGap/Continuum/SU2QuaternionProductHeatDualScore.lean:43` |
| `productHeat_normalized_dual_score_bound` | `lean/YMGap/Continuum/SU2QuaternionProductHeatDualScore.lean:86` |
| `qsum_sq_le_length_mul_qsumSquares` | `lean/YMGap/Continuum/RationalListCauchy.lean:81` |
| `coefficientL1_sq_le_length_mul_coefficientSquareSum` | `lean/YMGap/Continuum/SU2QuaternionAngularCoefficientSquareBudget.lean:72` |
| `productCurvatureCost_le_coefficientSquares` | `lean/YMGap/Continuum/SU2QuaternionAngularCoefficientSquareBudget.lean:115` |
| `productHeat_normalized_coefficientSquare_score_bound` | `lean/YMGap/Continuum/SU2QuaternionProductHeatCoefficientSquareScore.lean:54` |
| `productHeat_upperDirection_mean_zero` | `lean/YMGap/Continuum/SU2QuaternionProductHeatScoreCentering.lean:39` |
| `productHeat_upperDirection_center_congr` | `lean/YMGap/Continuum/SU2QuaternionProductHeatScoreCentering.lean:83` |
| `normalized_center_square` | `lean/YMGap/Continuum/SU2QuaternionProductHeatScoreVariance.lean:45` |
| `productHeat_normalized_coefficientSquare_variance_bound` | `lean/YMGap/Continuum/SU2QuaternionProductHeatScoreVariance.lean:66` |

## Parameters, multiplicities, and boundary cases

- n is arbitrary; selected indices satisfy i<n. Repeated selected factors
  are allowed and counted repeatedly. Empty products are covered.
- Angular terms may repeat, overlap, or have negative coefficients. Their
  raw local count is bounded by the displayed m. There is no global
  direction-count prefactor, but S still depends on the chosen coefficients
  and factor multiplicities. No volume-uniform operator estimate is asserted.
- Setting m=6 requires a proof of the local count. No theorem in this
  checkpoint canonically regroups an arbitrary raw list into six planes.
- The analytic guard is `0<w<1` and `relativeCutoff w 32 <= K`.
  C(w) is `logCurvatureCap w hw0 hw1`, defined in
  `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:148`:
  `C2(w)/headFloor(w) + relativeCap(w,32)^2`, with
  `C2(w)=4096*prefixBudget(w,6)+128*prefixBudget(w,4)`.
  There is no K or n in this cap, but its nome dependence is explicit and
  no useful w->1 asymptotic or physical beta/spacing calibration is proved.
- Mean zero allows signed a and arbitrary w,K. The variance INEQUALITY
  still uses the original positivity, cutoff, support and mass guards.

## The next join is not yet proved

The new estimate concerns a LINEAR KERNEL-SCORE RESPONSE. It is not a
quadratic Wilson temporal jump-energy estimate. A variance RHS does not
identify the quantities on the left, reverse the response inequality, or
bound the angular energy of the full source times observable.

The original finite-P source correction is still present in
`BF4ExactSlabFixedSpatialGroundStateEnergy.energy_eq_bare_add_correction`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.
The inactive residual and signed correction also remain in
`energy_le_fringeResidual_add_angular_add_correction` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedAngularEnergy.lean:106`.
The separate single-loop result `joint_increment_nome_bound` at
`lean/YMGap/Continuum/BF4WilsonAllNomeKineticIncrement.lean:168` does not
supply a collective response/energy identification.

Next: prove a useful actual Wilson response/energy join and source control,
or reassess this score route if it cannot supply them. Do not extend the
interface merely by assuming the desired temporal comparison. Spatial and
spacing control, nontrivial continuum survival, physical time/generator,
finite positive physical mass, full same-theory QFT/YM fields and every
compact simple group remain OPEN. No canonical frontier field was changed.

## Verification boundary

Eleven focused leaf checks, serialized through `scripts/safe_lean_build.py`,
one worker with an 8 GiB ceiling. Thirty-three printed load-bearing gates
report only permitted axioms {propext, Quot.sound}. Accepted logs have no
error, warning, `sorryAx` or `Classical.choice`. No new source hole or axiom.
The semantic root imports the final consumer; the root itself was NOT built.
No full-tree build, axiom audit, guard or progress-metric script was run.

Accepted local logs (each command completed with exit status zero):

```
/tmp/ym-gap-relative-polynomial-interval-check-2.log
/tmp/ym-gap-signed-heat-log-curvature-check-1.log
/tmp/ym-gap-signed-angular-locality-check-2.log
/tmp/ym-gap-product-heat-positive-floor-check-2.log
/tmp/ym-gap-product-heat-signed-curvature-check-2.log
/tmp/ym-gap-product-heat-dual-score-check-1.log
/tmp/ym-gap-rational-list-cauchy-check-2.log
/tmp/ym-gap-angular-coefficient-square-budget-check-3.log
/tmp/ym-gap-product-coefficient-square-score-check-1.log
/tmp/ym-gap-product-score-centering-check-2.log
/tmp/ym-gap-product-score-variance-check-1.log
```

Sol drafted the finite coefficient-budget and mean-zero/centering proofs;
Luna supplied the finite Cauchy draft and reviewed scope. Root integrated,
repaired and serially checked the drafts, proved the actual coefficient-square
and centered-variance consumers, and maintained the explicit frontier boundary.
