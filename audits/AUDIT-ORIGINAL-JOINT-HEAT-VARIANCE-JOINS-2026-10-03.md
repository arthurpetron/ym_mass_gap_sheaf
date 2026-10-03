# ORIGINAL joint-heat variance joins

## Outcome and scope

PROGRESS after `7700c2e`: four finite joins are now kernel-checked, preserving
the original source, existing output, shared tail and literal heat factors.
They supply true weighted conditional algebra for active-product Poincare,
not an interacting relative bound or a physical spectral gap.

The unchanged whole-project target remains OPEN: nontrivial constructive
continuum Yang--Mills on R^4 for EVERY compact simple group, SAME-theory
required QFT axioms and a finite positive physical Hamiltonian gap.
Canonical displayed claims and chart bytes are unchanged; no ASCII reprint.

## Forward constructions

All paths below are under `lean/YMGap/Continuum/`.

`SU2QuaternionSelectedConditionalPoincare.lean:97`
`selectedMean_conditional_pin` identifies the ACTUAL in-place projection
`project 0 (heatAt 0 1 w K * p)` with the lifted original conditional heat
under EVERY insertion. `selectedVariance_conditional_pin` (:113) preserves
its actual own-mean square. `selectedVariance_weighted_pin` (:138) and
`selectedAngular_weighted_pin` (:146) give the exact scalar Fubini joins.
`selectedConditional_weighted_angular_variance` (:163) proves the original
slot-0/1 variance bound with coefficient `1-w*w`. The source may depend on
output 1 and all spectators; the certified surrounding W need only be
independent of INPUT 0. Its dropped-head certificate is constructed by
actual partial integration. Guards are tail>0, 0<w<1, source support and
the previously computed fixed-source `poincareCutoff tail p <= K`.
Arbitrary-pair transport is NOT proved here, and the refuted universal
selected-link headMap identification is not used.

`SU2QuaternionWeightedHeatProjection.lean:91`
`heatUpdate_weighted_pairing` derives conditional orthogonality in the
ORIGINAL law `heatAt(i,j)*R`. R may depend on the existing output j and
every spectator, but is independent of input i; the test has the same
input independence. `heatResidual_weighted_orthogonal` (:139) centers the
actual source. `heatUpdate_weighted_square_decomposition` (:164) proves
exact Pythagoras, retaining signed R and all cross terms until orthogonality
removes them. These identities use source/weight/test support, distinct
valid original coordinates and tail>0; nome and cutoff are unrestricted.
Normalization is original `FullHeatTubeVacuum.pair_vacuum`, not a false
free-coefficient unit polynomial. `heatJointCertificate` (:203) constructs
the positive actual heat/R product from the existing floor certificate;
`heatUpdate_weighted_square_le` (:217) proves coefficient-ONE Jensen under
0<w<1, `headCutoff w <= K` and a constructed Certificate R. The heat factor
occurs exactly ONCE. No desired norm or variance inequality is a premise.

`SU2QuaternionProductHeatSweepResidual.lean:32`, :39 and :50
`weightedSweep_congr`, `weightedSweep_add`, `weightedSweep_neg` prove literal
coefficient linearity. `update_sweep_comm` (:78) commutes the actual lower/
upper-pair update through the sweep, including repeated or empty schedules.
`residual_sweep_comm` (:97) identifies each intermediate residual as the
sweep of the ORIGINAL-input residual. Source/output dependence is arbitrary;
only pair indices and sweep indices must lie below n. This is the exact
fixed-source algebra needed to avoid fresh Poincare cutoff guards on
intermediate swept sources. It is not itself an energy bound.

## Backward variance consumer

`SU2QuaternionConditionalVarianceTower.lean:53`
`determinant_variance_pin` uses actual arbitrary-insertion mass one to pin
the unnormalized determinant to its normalized own-mean expression.
`variance_certificate` (:64) transports the ORIGINAL two-copy square
certificate, and `weighted_jensen` (:81) retains arbitrary certified output R.
`tower_mean_pin` (:114) gives coefficient-strength Fubini for the literal
joined weight `W*liftBoundary inner R`. `variance_tower_pin` (:133) proves
EXACT total variance: variance of the conditional mean plus averaged inner
variance. No sign, independence or unit hypothesis is needed for this
polynomial identity; no signed cross term is silently discarded.
`tower_mass_pin` (:172) DERIVES joined carrier mass one from the two actual
conditional mass pins. `determinant_tower_pin` (:187) retains precisely
the determinant format consumed by the reference-variance node.

Independent Luna algebra/evidence review passed for the tower; independent
Sol mathematical review passed for joint-weight Pythagoras and fixed-source
residual commutation. Parent reviewed the selected Poincare/Fubini join.

## Exact next frontier and derivative currency

OPEN: the width-free Efron--Stein bound in the JOINT heat law, composed from
the newly proved local weighted Pythagoras/contraction and exact residual
commutation. Apply one-link Poincare to the ORIGINAL p with external W and
ALL other positive heat factors as its surviving weight. This avoids a
link-count penalty and avoids Poincare estimates on altered sweep sources.
Arbitrary-pair selected Poincare transport and its finite maximum of
fixed-original-source chart cutoffs remain OPEN.

The actual consumer is `projectedReferenceVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:83`),
with p=`lastStepProjectedDerivative` at the ORIGINAL K. Only the auxiliary
variance kernel uses L. The near-unit cutoff leg is already proved in
`projected_variance_cutoff_weighted_le` (same file :133).

The source is a constructed lower-fringe family projection, with actual
inactive-input independence supplied by `familyProject_independent`
and the carrier identities in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean`.
Inactive UPPER variables remain shared tail spectators; they are not erased.

This p is already a first derivative. Its Poincare energy Gamma(p) is a
SECOND-derivative quantity, not the p^2 sum called
`projectedDerivativeAngularBudget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`).
An actual estimate joining that energy to the SAME surviving-norm signed
cost remains necessary, together with BOTH Taylor terms and a JUSTIFIED
changing-family window. Physical/OS/continuum/QFT/every-group/Clay remain OPEN.

## Verification boundary

Four final focused checks, parent-serialized through safe_lean_build.py,
passed 32 gates, each within {propext, Quot.sound}, without warnings/errors
or sorryAx. Each launch had fresh process/swap/memory-pressure reads:
no competing compiler, 76--77% free memory and zero swap. One worker,
20 GiB worker ceiling and 12 GiB reserve; no resource escalation.
Earlier failed root checks were namespace/implicit-middle repairs only,
not accepted evidence. No sorry, axiom, Classical, Mathlib, native_decide,
weakened field or CI change. Root imports are registration ONLY; no full
root/tree build, broad guard, full axiom audit or progress metric is claimed.

| target | accepted log under `/tmp/` | gates | source SHA256 | log SHA256 |
| --- | --- | --- | --- | --- |
| ConditionalVarianceTower | `ym-conditional-variance-tower-20261003-3.log` | 8 | `1bd813676a0b1d79abc93a61a9bc878f1cedda80896d63086dccbd4e2c95aaff` | `c05a5ae19c59e62dcbe9801ef7459c41fddb6c0789660598ca46761069ad82e5` |
| SelectedConditionalPoincare | `ym-selected-conditional-poincare-20261003-1.log` | 7 | `58ed0957217435b3d4da000e859cfae56b4a2823464afaafe353d8f1f34d6751` | `8469fbb32a22647a9b5e4b0845ede94208c7d8da14d2cbd08a8df0dff7a242aa` |
| WeightedHeatProjection | `ym-weighted-heat-projection-20261003-1.log` | 11 | `41b476399a2ac10747d60eccfd3af90b863417e57ae55b3523cfe600b2825f08` | `215382252cd5d79ef24601fbd71d8252ac6d8ee8f248d06409ec759520b496a9` |
| ProductHeatSweepResidual | `ym-product-heat-sweep-residual-20261003-3.log` | 6 | `d02266687bbcead139bd86b8259f4c4d96f98709b7f2d6f1abef669db2bbf433` | `1bc981d480a6ca188bd1c7177349b71f771268f12b4d20d1a94a25ce771585e1` |
