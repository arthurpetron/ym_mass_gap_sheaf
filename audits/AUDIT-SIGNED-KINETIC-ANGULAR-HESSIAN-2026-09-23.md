# Whole signed-direction kinetic Hessian on the original SU(2) carrier

## Outcome and mathematical proof

For the actual selected finite product-heat kernel W, its integral operator P,
a supported signed source a, and any finite rational signed combination D of
in-range quaternion angular generators, the new result is

```text
H_2n[a(x) a(y) D_y^2 W(x,y)] = -H_n[(D a) P(D a)] <= 0.
```

The equality holds at every rational w and finite K. Nonpositivity requires
only `0 <= w`, exactly where the existing product-map pairing is positive
semidefinite. Selected indices must lie in the original n-block slice;
repetitions are allowed. There is no pointwise heat-floor/cutoff-onset,
centering, positive-source, normalized-mass or family-size premise.

The causal proof is:

1. The original relative scalar is the dot product of its two quaternion
   arguments. Simultaneous equal rotations leave it unchanged. The actual
   character chain rule and finite heat sum transfer this invariance to W.
2. Original product-Haar integration by parts in an arbitrary block makes
   the SAME product-heat pairing skew for each generator and then for D.
   Thus `B(a,D^2 a) = -B(D a,D a)` with all mixed terms retained.
3. The computed upper-slice direction differentiates only the lifted factor
   in `a(x) r(y)`. Twice integrating by parts moves the kernel derivatives
   onto the original upper source. The actual `productMap_pairing` joins the
   two-slice integral to step 2; positivity of B supplies the sign.

## Source map

All paths below are relative to the repository root.

| Declaration | Source | Role |
| --- | --- | --- |
| `derivative_self_carrier` | `lean/YMGap/Continuum/SU2QuaternionAngularCoordinate.lean:46` | Correct constant derivative after trailing-zero padding |
| `angular_coordinate_carrier` | `lean/YMGap/Continuum/SU2QuaternionAngularCoordinate.lean:73` | General coordinate-plane derivative |
| `partialHaarHeads_angularDerivative_at_zero` | `lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:46` | Coefficientwise cancellation in any containing Haar prefix |
| `angular_pair_at` | `lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:120` | Arbitrary-block original-Haar IBP |
| `angularDerivative_liftBoundary` | `lean/YMGap/Continuum/SU2QuaternionAngularLift.lean:56` | Exact upper-slice derivative shift |
| `scalarAt_pairedAngular_carrier_at` | `lean/YMGap/Continuum/SU2QuaternionRelativeHeatAngularInvariant.lean:189` | General supported scalar invariance |
| `heatAt_pairedAngular_carrier_at` | `lean/YMGap/Continuum/SU2QuaternionRelativeHeatAngularInvariant.lean:224` | All-cutoff actual relative heat invariance |
| `productHeat_pairedAngular_carrier` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularForm.lean:64` | Full original selected-product invariance |
| `kineticPair_angular_sum_zero` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularForm.lean:118` | Same-operator skew form |
| `AngularTerm` / `signedAngularDirection` | `lean/YMGap/Continuum/SU2QuaternionSignedAngularHeatResponse.lean:31`, `:43` | Explicit signed coefficients and finite in-range generators |
| `kineticPair_signedAngular_second_eq_neg_square` | `lean/YMGap/Continuum/SU2QuaternionSignedAngularHeatResponse.lean:158` | Entire source-side second response |
| `kineticPair_signedAngular_second_nonpositive` | `lean/YMGap/Continuum/SU2QuaternionSignedAngularHeatResponse.lean:182` | Same-form positivity consequence |
| `upperDirection_source` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:75` | Both endpoint sources retained |
| `signedAngular_haar_pair` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:98` | Whole signed-direction IBP |
| `productHeat_upperHessian_eq_neg_square` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:144` | Actual two-slice kernel Hessian identity |
| `productHeat_upperHessian_nonpositive` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:177` | Actual whole-direction sign |

The existing objects are `productHeat` and `productMap` in
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:53` and `:56`;
the actual two-slice join is `productMap_pairing` at `:247`. The existing
positivity consumer is `kineticPair_nonnegative` in
`lean/YMGap/Continuum/SU2QuaternionProductHeatDualForm.lean:75`.

## Exact verification boundary

Seven serialized monitored leaf checks used one worker and an 8 GiB hard
worker ceiling. Each accepted command exited 0. Twenty-four public axiom
print sites reported only `{propext, Quot.sound}`; accepted logs have no
warning, error, `sorryAx` or `Classical.choice`.

| Module suffix | Accepted log in `/tmp/` | Gates |
| --- | --- | ---: |
| `AngularCoordinate` | `ym-gap-angular-coordinate-check-2.log` | 2 |
| `HaarAngularIBPAt` | `ym-gap-angular-ibp-at-check-3.log` | 5 |
| `AngularLift` | `ym-gap-angular-lift-check-2.log` | 2 |
| `RelativeHeatAngularInvariant` | `ym-gap-relative-heat-angular-invariance-final-7.log` | 4 |
| `ProductHeatAngularForm` | `ym-gap-product-angular-form-final-3.log` | 2 |
| `SignedAngularHeatResponse` | `ym-gap-signed-angular-response-final-3.log` | 4 |
| `ProductHeatAngularHessian` | `ym-gap-product-angular-hessian-final-2.log` | 5 |

All module suffixes have prefix `SU2Quaternion` and directory
`lean/YMGap/Continuum/`. No full-root build, audit or guard was run. The new
Hessian leaf is imported into `lean/YMGap.lean`, but that root was not rebuilt.
CI remains off. No new `sorry`, axiom, classical quarantine or weakened
frontier field was introduced.

Early drafts are not accepted verification: these included missing namespace
opens, unelaborated terms, and a false raw coefficient-equality formulation
of scalar invariance. The final proof uses Haar-carrier equality instead.
An iff-based simplification introduced `Classical.choice`; explicit decidable
coordinate cases removed that dependency before the final consumer checks.
Sol supplied IBP/lift/direction and source-join drafts; root repaired,
constructed the general invariance and full kernel-Hessian consumers, and
checked the chain. A parallel read-only reviewer confirmed the same-kernel,
same-source scope and the quantitative boundary.

## Open mathematical join and unchanged project goal

This proves an integrated sign, not a coefficient-square upper bound on
Wilson jumps or a normalized comparison with the SAME centered variance.
It does not construct a reciprocal/logarithmic kinetic-score test or estimate
its second derivative. It does not identify the finite-P endpoint correction
with an angular Laplacian or control that correction in
`BF4ExactSlabFixedSpatialGroundStateEnergy.energy_eq_bare_add_correction`.

Next: derive a quantitative cancellation-preserving consequence for the
original normalized temporal form with complete a=V*g, and justify its
comparison to the original variance on an actual scaling family. No claim
is made that the new sign alone suffices for that step.

Spatial/spacing limits, nontrivial continuum survival, finite positive
physical Hamiltonian mass, full same-theory OS/QFT/YM local-field and UV
identification, and every compact simple group remain OPEN. No canonical
Clay frontier atom is closed by this milestone.
