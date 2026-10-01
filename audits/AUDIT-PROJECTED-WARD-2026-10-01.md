# Original marginal Ward transport

The checked result transports the **integrated Ward residual** of the original
odd marginal to a projected-source angular-gradient pairing, for padded spatial
families with arbitrary signed coefficients and repeated faces. It rewrites
the actual complete centered error without changing its mean, partition or
negative coefficient. It supplies no sign, smallness or scaling estimate.

## Declarations and actual consumer

All new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedWard.lean`:

| Declaration | Line | Checked content |
| --- | --- | --- |
| `projectedPairWeight` | 74 | Auxiliary polynomial `q*P(q)`, not the original marginal. |
| `wardResidual_projected_pair` | 143 | Equality of the integrated residuals, with the original mean. |
| `normalizedWardResidual_projected_pair` | 207 | Same equality normalized by the original `oddMass`. |
| `completeCenteredError_projected_pair` | 227 | Rewrites the existing complete error with its unchanged coefficient `-(1-w)`. |

The original `completeCenteredError` is defined at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:285`.
Its useful bound relative to the SAME interacting variance on a justified
changing-coupling/spatial/spacing family remains open.

## Mathematical argument

`oddMoment_projected_source`, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:117`,
transports the independent centered test `(f-center)*f`.
`angular_moment_pin`, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAngularMarginal.lean:65`,
transports each angular square. Applying `complete_ward_raw`, at
`lean/YMGap/Continuum/SU2QuaternionWeightedCasimirWard.lean:235`, to both
weights and using the spatial family's Casimir identity cancels their equal
angular energies and Casimir moments. The remaining integrated residuals agree.

The original weight is `V*g_n*g_(n+1)`. No declaration identifies it
coefficientwise with `q*P(q)` or transports its derivatives pointwise.

## Verification boundary

The final focused monitored check succeeded and emitted the target `.olean`.
All four gates report exactly `{propext, Quot.sound}`. The accepted log is
`/tmp/ym-original-projected-ward-consumer-20261001.log`, SHA256
`72b36efb875c6ac612b2be2158814a621f32b366519530d900b43f2f8fff544d`.
Independent source/log review passed. One worker, 20-GiB ceiling and 12-GiB
OS reserve were retained. No full-tree build, audit or guard was run.

No new `sorry`, axiom, analytic premise or weakened frontier was introduced.
Continuum survival, physical time/mass, full QFT, every group and the Clay
target remain open. No displayed chart claim changes.
