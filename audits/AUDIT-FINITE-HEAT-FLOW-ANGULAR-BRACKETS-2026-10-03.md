# Actual angular brackets and finite heat-flow endpoint

## Purpose and proof boundary

Two concrete mathematical prerequisites for the next reference conditional
variance estimate are now checked. Neither assumes that estimate, substitutes
a theory, or supplies the original signed-window/scaling budget. The previous
checked near-unit cutoff comparison remains in
`audits/AUDIT-ORIGINAL-ACTIVE-VARIANCE-CUTOFF-2026-10-03.md`.

## Actual angular Lie brackets

All declarations in this section are in
`lean/YMGap/Continuum/SU2QuaternionAngularLieBracket.lean`.
For the actual fields D_ij=x_i*partial_j-x_j*partial_i,
`overlapping_planes_bracket` (:106) proves

```text
[D_ij,D_jk]p = D_ik p
```

as `HaarCarrierEqv blocks`, for 0<blocks, three pairwise distinct indices
i,j,k<4 and arbitrary signed p. Every other block remains a shared spectator;
no support restriction on p is added. The proof expands the actual Leibniz
rule and cancels the mixed jets using `ratDerivative_comm`,
`lean/YMGap/Continuum/SU2QuaternionDerivativeCommutation.lean:77`.
Actual coordinate derivative pins account for trailing-zero padding; a raw
coefficient identity that could distinguish such padding is not asserted.

`angular_plane_antisymmetry` (:181) and `disjoint_planes_commute` (:207)
prove the corresponding coefficient-strength identities. Disjointness means
the four cross-index inequalities in the statement, not a hidden locality
or spectator premise. The sign of the overlapping bracket is positive:
it sends x_k to x_i and x_i to -x_k.

Further actual HEAD angular differentiation preserves the carrier identity
by `angularDerivative_carrier`,
`lean/YMGap/Continuum/QuaternionHaarAngularCarrier.lean:57`; its nonempty
carrier and coordinate bounds remain required. Moving to another original
block still needs the actual supported reindex/exposure transport. This leaf
does NOT prove Casimir centrality, the ordered-square identity, Gamma2
positivity or a conditional Poincare inequality.

## Constructed finite heat-flow saturation and endpoint

All declarations in this section are in
`lean/YMGap/Continuum/SU2QuaternionHeadHeatFiniteFlow.lean`.
`inputCutoff` (:41) computes

```text
C(p)=headDegreeBound(sumHarmonics(modes(tail+1,p))).
```

It is explicit finite data for THIS polynomial. `headMap_saturated` (:52)
proves that, for K>=C(p), the actual `headMap(w,K,p)` is its complete
finite harmonic sum, with coefficient w^(d*(d+2)) on each grouped degree.
The equality is tested by EVERY Haar insertion, not just one scalar pairing.
`headMap_cutoff_stable` (:75) proves the same map for ANY two later K,L.
`headMap_one_reproduction` (:98) proves `headMap(1,K,p)=p` on this carrier
once K>=C(p), using the actual computed harmonic reassembly.

The original map is `headMap`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:247`, namely
conditionalHeat(copy(p)). The spare output is distinct and every spectator
is shared. The literal harmonic expansion comes from `headMap_grouped`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatSmoothing.lean:64`, and original
reassembly from `polynomial_harmonic_carrier`,
`lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:158`.

These identities require supported p but no nome positivity. Nome-one
reproduction is NOT positivity of the finite kernel at one. The cutoff can
grow when the ORIGINAL source changes; no changing-family uniformity follows.
Semigroup composition and nome-generator differentiation are NOT proved by
this leaf.

## Explicit remaining seams and next mathematical producer

Construct actual Casimir centrality and the six-field Bochner square; then
construct a conditional reference heat-flow variance inequality that retains
the original surviving variables and output weight. The source remains Q_K
from the original variance comparison, not an auxiliary Q_L. Its eventual
consumer remains the COMPLETE normalized original signed-window budget,
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.

Do not equate a fresh heat output with an existing shared variable by merely
invoking arbitrary insertions. `reindex_carrier` and `reindex_certificate`,
`lean/YMGap/Continuum/SU2QuaternionHaarCertificateReindex.lean:89` and :136,
are proved for Haar involutions, not noninjective diagonal substitution.
`substituteRetained_congr`,
`lean/YMGap/Continuum/SU2QuaternionDroppedHeadSubstitution.lean:67`, handles
coefficient equality. `substitute_copy_carrier`,
`lean/YMGap/Continuum/SU2QuaternionSpareHeadCopy.lean:246`, handles its special
copy reconstruction. A general diagonal certificate/carrier transport is
NOT FOUND in these modules. Either prove the needed particular unit-block
pullback or construct the final boundary-pinned conditional certificate
directly. Do not add an unnecessary general compiler when the latter suffices.

A generic rational polynomial/Laurent derivative-sign to endpoint-order
theorem was also NOT FOUND in the reviewed `Constructive/QPolyFormalDerivative`,
`QPolyCoefficientEvaluation`, `QPolyPositivePrimitive`, `QPolyUHRowPrimitive`,
`QPolyRootLogPositiveRows`, `Continuum/RiemannSOS`, `RiemannConverge` and
`BF4WilsonAllNomeMeshDerivative`. Formal derivative algebra and positive
u/h-row primitives are reusable pieces, not an already proved mean-value
bridge. A finite constructive order argument still needs an actual proof.

Intermediate auxiliary nomes approaching one cannot use positivity of a
single fixed finite kernel without proof. Saturation now permits comparing
to a larger computed positive prefix for each strict nome; the exact
endpoint is reproduction, not a positive-kernel assertion.

OPEN: the actual conditional angular variance estimate, signed action/Taylor
join in SAME surviving-norm currency, useful aggregate original window
budget, justified scaling family, physical survival/calibration, full
same-theory continuum QFT, every compact simple group and Clay closure.

## Focused verification

Two serialized checks exited zero, with seven gates all within
{propext, Quot.sound}. Accepted logs:

```text
/tmp/ym-angular-lie-bracket-20261003-2.log       (3 gates)
/tmp/ym-head-heat-finite-flow-20261003-1.log     (4 gates)
```

Each used `scripts/safe_lean_build.py --jobs 1 --reserve-gib 12
--check-worker-limit-gib 20 --status-seconds 300`, named source and explicit
olean output. Preflights found 74--76% memory free, zero swap and no competing
Lean worker. Accepted logs contain no errors, warnings, sorryAx or choice.
The first failed bracket elaboration is rejected, not proof evidence.
Independent source/math reviews passed both leaves. No new sorry/axiom,
weakened field, CI or exact-chart change; root imports are registration only.
No full/root build or full audit is claimed.

SHA-256 sources, bracket then finite flow:

```text
ecfead4a9eff7c5604763d0ca0433253cac3bb68a0e4e109b0911d116976416d
badf20e73396ca988dd448d9f7a93234215aae1f7fa5ea0044219db888e8c282
```

SHA-256 accepted logs, same order:

```text
7eec64010c094c73ffe1d42df350c6d0940aa87278414d6d8e76e09690a0ef7a
17ad3baaee32acdcd800533e112d1f67119423d58080d681b86752cc47ba3531
```
