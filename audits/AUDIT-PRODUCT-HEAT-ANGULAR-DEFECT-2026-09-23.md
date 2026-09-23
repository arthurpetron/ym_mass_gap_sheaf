# Original full-product angular defect without inter-step commutation

Date: 2026-09-23. Parent revision: `500e9ab`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT and
Yang--Mills local-field/short-distance structure, isolated vacuum and a finite
positive physical Hamiltonian mass gap.

## Actual quantitative endpoint

`productMap_range_defect_le_two_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularDefect.lean:161`, proves

```
H_n(p*p) - H_n(p * productMap n w K (List.range n) p)
  <= 2*(1-w) * sum_{i<n} H_n(blockAngularSquare i p).
```

Here n=tail+1, p is any supported signed rational quaternion polynomial,
`0 <= w < 1`, and `sufficientCutoff w <= K`. There is no centering,
pointwise heat-floor premise, assumed operator realization, or commutation
input. The coefficient `2*(1-w)` is independent of n and K; the sum still
contains n original-block energies. This is a defect upper bound, not a
strict spectral-gap lower bound.

The fully active ORIGINAL product is pinned by the existing
`productMap_range_cycle_carrier`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicFold.lean:144`.
The new `productMap_range_defect_le_rotated_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularDefect.lean:140`, consumes
this pin after the reference returns to the original p. The final theorem
then rewrites every rotating angular cost to its original block.

## Mathematical contraction of the proof path

For a symmetric positive contraction P, put D=I-P and
`Phi_x(y)=<y,y>-4<x,y>+3<x,x>`. Two nonnegative expressions suffice:

1. `D(2x-y,2x-y) >= 0`;
2. `<y,Py>-<Py,Py> >= 0`.

Adding them gives `Phi_x(Py)<=Phi_x(y)+4*D(x,x)`. Also
`Phi_x(y)=2*(<x,x>-<x,y>)+<x-y,x-y>`.
Telescoping from y=x therefore bounds the endpoint defect by twice the sum
of fixed-reference local defects. This avoids both inter-step commutation
and a joint spectral decomposition; no square root or spectral theorem is used.

The generic checked declarations are `potential_step`,
`lean/YMGap/Continuum/PositiveContractionProductDefect.lean:60`, and
`path_defect_bound`, same file line 119. They are actually consumed by
`cycleIterate_rotated_defect_le_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularDefect.lean:110`.
For cyclic step C=R headMap, both the evolving input and its reference rotate
by R. Haar isometry preserves the potential. The local costs are evaluated
on R^i p, not on a repeatedly smoothed substitute for p.

The remaining algebraic pins are:

- `rotateIterate_period_carrier`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicRotationPeriod.lean:122`:
  R^n p equals p under every Haar insertion on the supported n-block carrier.
- `rotateIterate_headAngularSquare_haar_of_lt`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicAngularEnergy.lean:84`:
  the head energy of R^i p is the original block-i energy for i<n.

Sol supplied the two rotation/transport drafts; root repaired elaboration,
checked the gates and proved the actual potential/product consumer. Luna
independently reviewed the algebra and final source scope.

## Consumer and remaining frontier

The sharper factor-one target remains OPEN and unchanged. This is a separate
proved factor-two theorem; no canonical field or existing statement is weakened.
Commutation/joint modes may sharpen the constant but are not prerequisites
for the theorem now proved.

The intended interacting consumer is `energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.
Its proper active list is NOT `List.range n`: inactive Haar projections must
still be accounted for. Its complete input is `V*g*f`, and its correction is
signed. In particular the factor-two bare estimate does not itself cancel
endpoint-source derivatives against that correction. The earlier exact
head-angular cancellation identity is not silently applied with a changed
coefficient. These are the next original-action obligations.

No claim is made about physical OS/time identification, spatial/spacing
uniformity, continuum survival, full QFT, physical mass or other groups.

## Verification boundary

Accepted serialized checks, all terminal exit 0, one worker and 8 GiB cap:

- `/tmp/ym-gap-product-defect-potential-check-2.log`: five gates;
- `/tmp/ym-gap-cyclic-rotation-period-check-2.log`: five gates;
- `/tmp/ym-gap-cyclic-angular-energy-check-1.log`: three gates;
- `/tmp/ym-gap-product-heat-angular-defect-check-2.log`: three gates.

All sixteen printed gates contain only `{propext, Quot.sound}` (one uses
only `propext`). Accepted logs contain no warning, error, `sorryAx` or
`Classical.choice`. Earlier elaboration-error drafts are not evidence.
No new `sorry`, axiom, classical exception or changed frontier field.
Root imports are registered; no full-root build/audit/guard was run.
CI remains unchanged.
