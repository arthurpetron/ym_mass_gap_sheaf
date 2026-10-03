# ORIGINAL product-angular Poincare and backward input-energy consumer

## Outcome and honest boundary

PROGRESS after `8f280d7`: the ORIGINAL joint product heat law now satisfies

```text
||p||_mu^2 - ||S_ids p||_mu^2
  <= (1-w^2) * sum_{i in ids} H[mu * Gamma_i(p)],
mu = liftBoundary n W * productHeat n w K ids.
```

S is the literal in-place conditional heat sweep on existing lower/upper
pairs. W,p, every heat factor and all shared outputs/spectators stay fixed.
There is NO link-count factor. One explicit finite maximum supplies the
fixed-original-source cutoff. This is a finite reference conditional bound,
not the SAME interacting norm-relative estimate or physical spectral gap.

The backward consumer also proves actual second-derivative energy contraction
under lower-fringe projection in the unchanged reference/output weight.
Original action/transfer/source K is distinct from auxiliary kernel L.

The unchanged whole-project target remains OPEN: nontrivial constructive
continuum Yang--Mills on R^4 for EVERY compact simple group, SAME-theory
required QFT axioms and a finite positive physical Hamiltonian gap.
Canonical displayed claims/bytes are unchanged; no ASCII reprint.

## 1. Actual arbitrary-pair transport

`lean/YMGap/Continuum/SU2QuaternionSelectedPairConditionalPoincare.lean:102`
`chain_project` transports actual conditional projection coefficientwise.
`chain_blockAngularSquare_prefix` (:141) transports the angular square by
actual block involutions. Supported-carrier promotion retains every original
insertion; no generic diagonal pullback or free-coefficient unit is used.
`pairChart` (:54) acts on the WHOLE original source and weight, exposing
distinct input i/output j simultaneously via `pairSteps`.
`selectedPairVariance_chart_pin` (:185) and `selectedPairAngular_chart_pin`
(:213) give the actual weighted scalar joins. The theorem
`selectedPair_weighted_angular_variance` (:251) proves the bound for arbitrary
source dependence on i,j and every spectator; only W is independent of i.
Guards: positive tail, distinct valid pair, 0<w<1, original source/weight
support, Certificate W and the computed `selectedPairCutoff` (:65).
This onset belongs to the charted FIXED source, not a changing source family.

## 2. Width-free ORIGINAL joint-law composition

`lean/YMGap/Continuum/SU2QuaternionProductHeatEfronStein.lean:59`
`jointWeight` keeps W and every original product heat factor. `jointSquare`
(:63) and `residualEnergy` (:67) use that SAME law and ORIGINAL p.
Actual selected-factor removal, rest support/independence and rest Certificate
are constructed from the erased distinct list; no analytic estimate is input.
`joint_update_square_decomposition` (:117) and `joint_update_square_le`
(:146) supply true local joint-law Pythagoras/contraction. The exact
`residual_sweep_comm` from the preceding milestone compares an intermediate
residual to the sweep of the original residual. Thus
`joint_sweep_efron_stein` (:234) bounds the actual sweep loss by the sum of
ORIGINAL-input residual squares with coefficient ONE, without volume loss.
Contained schedules may repeat; the fixed heat-factor list is Nodup/in-range.

`joint_residual_variance_pin` (:291) identifies each original residual norm
with the actual selected own-mean variance under ALL remaining heat factors
and W. `joint_residual_angular_le` (:353) applies the newly proved pair
Poincare to ORIGINAL p, not to changing intermediate sweep sources.
`jointAngularEnergy` (:267) is the exact original input-energy sum in mu.
`joint_sweep_angular_poincare` (:412) composes these inequalities without
source/weight substitution or a count factor.

`selectedLinkCutoff` (:246) is the actual pair-chart onset for valid inputs,
with invalid index branch zero. `jointPoincareCutoff` (:253) is
`max(headCutoff w, ids.foldr(max(selectedLinkCutoff n i p),0))`.
`joint_sweep_angular_poincare_at_cutoff` (:425) derives ALL needed stage/head
guards from this ONE computed onset. Empty/zero carriers and W=0 are included.
The head guard depends on nome, the chart onsets depend on source/carrier;
no changing-source, spacing, spatial or coupling-family uniformity is claimed.

## 3. Backward: genuine second-derivative currency

`lean/YMGap/Continuum/SU2QuaternionHaarFamilyWeightedAngularContraction.lean:40`
`familyProject_weighted_blockDerivative_square_le` uses exact distinct-block
commutation and the original weighted square contraction. Derivatives in a
projected block vanish coefficientwise. `familyProject_weighted_blockAngularSquare_le`
(:65) and `familyProject_weighted_angularSum_le` (:79) sum with coefficient one,
retaining the SAME certified weight independent only of projected slots.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedInputAngularEnergy.lean:57`
`inputAngularReferenceEnergy` is literal partial integration of
`kineticWeight(w,L)*Gamma_input(p)`. `projectedInputAngularEnergy` (:61)
uses the complete ORIGINAL first projected source derivative at K;
`sourceInputAngularEnergy` (:66) retains the unprojected complete derivative.
`inputAngularReferenceEnergy_pairing` (:101) gives exact Fubini with
`kinetic_L * lift W`. `projected_inputAngularEnergy_weighted_le` (:124)
constructs that weight's Certificate and its actual lower-fringe independence,
then contracts the SECOND-derivative energy with coefficient one.
The actual V_K and BOTH transfer_K source terms remain untouched.
Only the auxiliary positive reference kernel uses L, with `headCutoff w <= L`.
Arbitrary certified output W is retained, including zero.

## 4. Remaining causal frontier

OPEN: exact weighted joint sweep-loss to the own determinant variance of
`projectedReferenceVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:83`).
Inactive lower integration cannot be discarded for arbitrary p. The actual
BF4 projected source has proved inactive lower-fringe independence, while
inactive upper variables remain shared spectators. Use those exact pins to
close the weighted endpoint before claiming the full reference-variance node.

Then instantiate the fixed-source onset at auxiliary L for original Q_K.
The near-unit K/L variance comparison is already proved in
`projected_variance_cutoff_weighted_le` (same file :133).

Gamma(Q_K) is SECOND derivative and is NOT the Q_K^2 sum
`projectedDerivativeAngularBudget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`).
This increment contracts energy-to-energy; it does NOT supply useful
energy-to-SAME-surviving-norm control, BOTH signed Taylor terms, or a JUSTIFIED
changing-family window. Those and physical/OS/continuum/QFT/every-group/Clay
remain OPEN. No canonical frontier bundle is inhabited by this increment.

## 5. Exact verification

Four FINAL focused checks passed 32 gates within {propext, Quot.sound},
including the axiom-free jointWeight definition. No warnings/errors/sorryAx.
Independent Sol reviews passed for pair transport, the final product-angular
join and backward energy contraction; Luna checked source/evidence boundaries.
Parent alone compiled, serialized through safe_lean_build.py: one worker,
20 GiB worker ceiling, 12 GiB reserve. Fresh process/swap/memory-pressure
reads preceded EVERY launch: no competing compiler, 76--77% free, zero swap.
No resource escalation. Earlier failed checks were a missing namespace and
code-generator List.rec repair by actual structural witness recursion; they
are NOT accepted evidence. No sorry/axiom/Classical/Mathlib/native_decide,
weakened field or CI change. Root imports are registration only; no full
root/tree build, broad guard, full axiom audit or progress metric is claimed.

| target | accepted log under `/tmp/` | gates | source SHA256 | log SHA256 |
| --- | --- | --- | --- | --- |
| SelectedPairConditionalPoincare | `ym-selected-pair-conditional-poincare-20261003-2.log` | 9 | `a89f1727e0b0deab3af29f24bcb33e5adc3203f230b4dbe1909be82e75fc8230` | `db6123c30ddd6505f68a3fbd008083e82cba51a834b9830636583dcaf02e2b0b` |
| ProductHeatEfronStein | `ym-product-heat-efron-stein-angular-20261003-1.log` | 15 | `8d18a0b5f357251da6a315ce2c8da20a4721ca659f7da1260baf2d65e82c1372` | `26d369618e05ad7e1a9064b5c240c5cb300c044e615a209f2ba5c68d870c4c04` |
| HaarFamilyWeightedAngularContraction | `ym-family-weighted-angular-contraction-20261003-1.log` | 3 | `021a9ae3115b8261280b5f7d0209369efd6e0fd43634ee1ad680f6e648a06120` | `6ac55249255dabe5ca4994d6f49f03a29aa16a811d9603efa5ae8b0b178d08dc` |
| BF4ProjectedInputAngularEnergy | `ym-projected-input-angular-energy-20261003-1.log` | 5 | `27ef60a3e10f18611a993ad4759a7fed527e4aab328bda0e778af5dd05f8d300` | `09314325b650b734821d280c06b7b649555104c09bc75a8cbd52374b7fe36211` |
