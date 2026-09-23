# Inactive Haar projection and the original interacting energy

Date: 2026-09-23. Parent revision: `a949762`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT and
Yang--Mills local-field/short-distance structure, isolated vacuum and finite
positive physical Hamiltonian mass gap.

## Checked mathematical increment

Write H for the original n-block quaternion Haar functional, F for the
inactive coordinate list, A for the active list, E_F for the concrete family
Haar projection, q=E_F f and r=f-q. With a proved permutation
`(F++A).Perm (List.range n)`, the original partial-product form defect obeys

```
H(f*f)-H(f*P_A f) = H(r*r) + H(q*q)-H(q*P_full q).
```

This is `productMap_defect_eq_residual_add_full`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatInactiveAngularDefect.lean:45`.
For n=tail+1, supported signed f, rational `0 <= w < 1`, and
`sufficientCutoff w <= K`, the same module's
`productMap_defect_le_projected_angular` at line 70 consequently gives

```
H(f*f)-H(f*P_A f)
  <= H(r*r) + 2*(1-w)*sum_{i<n} H(blockAngularSquare i q).
```

Only the prefactor is independent of n,K. The residual, the sum and the
original input remain explicit and may depend on the geometry and cutoff.
This is an UPPER bound on a defect, not a coercive spectral-gap lower bound.

## Exact producers

- `family_square_decomposition`,
  `lean/YMGap/Continuum/SU2QuaternionHaarFamilyPythagoras.lean:75`,
  proves ordinary-Haar Pythagoras from actual projection orthogonality.
  `familyProject_square_le`, same file line 116, bounds the projected square
  by the original square with coefficient one for supported inputs.
- `productMap_family_input_pairing`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatInactiveProjection.lean:43`,
  projects inactive input coordinates without changing any original pairing.
  `productMap_family_quadratic_pairing`, same file line 68, projects both
  occurrences of the input against the SAME kernel.
- `productMap_inactive_to_full_pairing`, same file line 105, restores the
  missing heat factors on the projected input using their vacuum marginal.
  It uses the supplied actual cover permutation, not a cardinality estimate.

These identities require no positivity or cutoff guard; their explicit range,
cover and support premises are retained where needed. The inequality uses
the existing full-product angular estimate with its original guards.
`productMap_defect_le_angular_of_independent`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatInactiveAngularDefect.lean:89`,
removes the projection only under proved independence of the COMPLETE input.

## Actual interacting consumer

`energy_le_fringeResidual_add_projectedAngular_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedAngularEnergy.lean:58`,
applies this result to the actual active/fringe partition and
`u=(endpointSource w K width g)*f=(V*g)*f`. It proves

```
energy(w,K,width,g,f)
  <= H((u-E_F u)^2)
     + 2*(1-w)*sum_i H(blockAngularSquare i (E_F u))
     + correction(w,K,width,g,f).
```

The support of g,f and `0 < (baseLinks width).length` are explicit. The
existing `labels_perm_range` supplies the physical list partition. The
consumer combines the bound with the exact
`energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.

The residual here is ordinary Haar applied to the entire u. It is NOT the
different weighted `spatialFringeResidual` of f. No sign or cancellation of
the endpoint correction is proved. The factor-two inequality does not permit
silently applying a factor-one product-rule cancellation.

## Remaining mathematical frontier

Next is angular-energy contraction under the inactive Haar projection,
followed by actual source-derivative, residual and signed-correction estimates
relative to the original normalization. These are not proved by writing their
terms explicitly. Physical time/OS identification, volume/spacing control,
continuum survival, finite positive mass, full QFT/local fields and every
group remain OPEN. No canonical frontier field is changed or discharged.

## Verification boundary

Four accepted serialized single-worker 8 GiB leaf checks, terminal exit 0:

- `/tmp/ym-gap-haar-family-pythagoras-check-1.log`: five public gates.
- `/tmp/ym-gap-product-inactive-projection-check-4.log`: four public gates.
- `/tmp/ym-gap-product-inactive-angular-defect-check-1.log`: three public gates.
- `/tmp/ym-gap-fixed-spatial-projected-angular-energy-check-2.log`: one gate.

All thirteen gates report only `{propext, Quot.sound}`. Accepted logs contain
no warning, error, `sorryAx` or `Classical.choice`. Earlier failed drafts do
not count as verification: the core `List.nodup_range` introduced a classical
dependency, repaired using existing constructive `CayleyParentInj.range_nodup`;
the consumer's first check failed on the misspelled `List.Perm.append_comm`,
repaired to `List.perm_append_comm` without changing its statement.

Sol supplied the Pythagoras and consumer drafts; root proved the original
pairing joins, composed and checked all leaves; Luna reviewed scope. Root
imports are registered. No full-root build, audit or progress guard was run.
No new `sorry`, axiom, classical exception or weakened frontier statement.
