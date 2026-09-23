# Angular energy decreases under the actual family Haar projection

Date: 2026-09-23. Parent revision: `76ddc32`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT and
Yang--Mills local fields/short-distance structure, isolated vacuum and finite
positive physical Hamiltonian mass gap.

## Actual estimate and proof

For supported signed polynomial f on n quaternion blocks, and any finite
in-range list F (repetitions allowed), write E_F for the existing in-place
conditional Haar projection. The checked inequalities are

```
H(blockAngularSquare i (E_F f)) <= H(blockAngularSquare i f),  i < n;
sum_{i<n} H(blockAngularSquare i (E_F f))
  <= sum_{i<n} H(blockAngularSquare i f).
```

The prefactor is ONE. There is no heat parameter, cutoff, centering or
pointwise positivity premise. These are
`familyProject_blockAngularSquare_le` and `familyProject_angularSum_le`,
`lean/YMGap/Continuum/SU2QuaternionHaarFamilyAngularContraction.lean:136`
and line 149, respectively.

The proof has two cases for each block. If it is averaged, all of its angular
derivatives vanish. If not, differentiating it commutes with every selected
Haar projection. The square of the averaged derivative is bounded by the
original square using the preceding actual Haar Pythagoras. Sum the six
coordinate-plane derivatives, then the n block energies.

The algebraic producer is `ratDerivative_project_of_ne`,
`lean/YMGap/Continuum/SU2QuaternionSelectedHaarDerivative.lean:127`.
It follows from `lowerExponentAt_clearQuaternionBlock_of_ne`, same file
line 61, and `quaternionBlockMoment_lowerExponentAt_of_ne`, line 91.
The monomial's coordinate positions are retained; integration is not replaced
by the coordinate-deleting head operation. Family angular commutation is
`blockAngularDerivative_familyProject`,
`lean/YMGap/Continuum/SU2QuaternionHaarFamilyAngularContraction.lean:76`.

## Original-operator consumers

`productMap_defect_le_residual_add_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatInactiveAngularDefect.lean:113`,
now gives

```
H(f*f)-H(f*P_active f)
  <= H((f-E_F f)^2) + 2*(1-w)*sum_i H(blockAngularSquare i f).
```

It keeps all earlier partition, support, positive block-count, rational
`0 <= w < 1` and `sufficientCutoff w <= K` guards. No independence of f is
assumed and its residual is not discarded.

`energy_le_fringeResidual_add_angular_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedAngularEnergy.lean:106`,
uses the contraction directly on the previously proved interacting estimate:

```
energy(w,K,width,g,f)
  <= H((u-E_F u)^2)
     + 2*(1-w)*sum_i H(blockAngularSquare i u)
     + correction(w,K,width,g,f),   u=(V*g)*f.
```

This is the angular energy of the COMPLETE source u, not f alone. The
ordinary-Haar residual is also of u, not the different weighted spatial
residual. The signed correction is unchanged. Replacing projected angular
cost by unprojected cost is an upper-bound consequence, not a claim that the
new numerical right side is smaller.

## Remaining frontier

Source derivatives, inactive residual and signed endpoint correction must
still be estimated relative to the actual normalization with all relevant
cancellations preserved. The correction contains f^2; a factor-two bound on
the bare endpoint form does not automatically cancel it. The present result
is an energy UPPER bound, not a spectral-gap LOWER bound. Physical OS/time,
volume/spacing control, continuum survival, finite positive mass, full QFT
and every-group joins are unchanged and OPEN.

## Verification

Accepted serialized single-worker 8 GiB leaf checks, all terminal exit 0:

- `/tmp/ym-gap-selected-haar-derivative-check-3.log`: three public gates.
- `/tmp/ym-gap-haar-family-angular-contraction-check-3.log`: four public gates.
- `/tmp/ym-gap-inactive-original-angular-defect-check-1.log`: four gates.
- `/tmp/ym-gap-fixed-spatial-original-angular-energy-check-1.log`: two gates.

All thirteen gates (including unchanged consumers) report only
`{propext, Quot.sound}`. Accepted logs have no warning, error, `sorryAx` or
`Classical.choice`. Failed elaboration drafts are not verification evidence.
Sol supplied the termwise derivative draft; root repaired and checked it,
proved the angular and original-energy consequences, and registered imports;
Luna reviewed inequality orientation and scope. No new hole, axiom,
classical exception or weakened frontier field. No full-root build/audit or
progress guard was run.
