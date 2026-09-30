# Original conditional residual: energy-relative approximation

Date: 2026-09-30 UTC. Parent source baseline: `1dc8b5f`.

## Mathematical result

Fix the original SU(2) full action, 0<w<1, finite extent and late heat
cutoff K>=headCutoff(w). Let P_i be its actual completed conditional
projection, R_i=I-P_i, and q=inverseRate(w). For every supported polynomial
p, use the EXISTING polynomial kernel test t_i(a_n p), with a_n the
constructed exterior reciprocal approximant. The new theorem proves

```
||R_i p - t_i(a_n p)||^2 <= q^(2n) ||R_i p||^2.
```

The earlier bound had ||p||^2 on the right. The proof does not posit a
spectral gap or a positive lower bound for the particular residual.

Declarations in
`lean/YMGap/Continuum/BF4ExactSlabStarEnergyRelativeApproximation.lean`:

| Declaration | Line | Content |
| --- | --- | --- |
| `residual_error_sub_probe` | 123 | Subtracting any finite exterior prediction leaves the actual completed approximation error exactly unchanged. |
| `residual_approximation_energy` | 144 | The geometric error bound has the original residual-energy prefactor. |
| `residual_energy_relative_error_le` | 169 | The existing explicit relative cutoff gives error <=epsilon times local residual energy. |
| `residual_energy_relative_bracket` | 190 | The existing computable rational dual value V satisfies V<=E_i<=V+epsilon*E_i. |
| `summed_residual_energy_relative_error_le` | 217 | For any finite list of links, the sum of local squared errors is <=epsilon times the original sum of residual energies. |

## Proof and constructive data

For a finite exterior polynomial b, the error identity is
`R_i((1-D*a_n)*(p-Jb))`. Exterior multiplication preserves exterior
probes, so R_i kills its Jb term exactly. Apply the already-proved
norm-relative estimate to p-Jb and let Jb approach P_i p through the
EXISTING constructed conditional-output sequence. Its squared distance
to p converges to ||R_i p||^2. No representative is selected from a
quotient, and no positivity decision or division by E_i occurs.

Relevant existing inputs:

- `residual_error_identity` and `residual_approximation_norm`,
  `lean/YMGap/Continuum/BF4ExactSlabStarResidualApproximation.lean:142`
  and `:177`.
- `conditionalDenseMap` and `conditionalProjection_embed`,
  `lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:213`
  and `:225`.
- `relativeCutoff`,
  `lean/YMGap/Continuum/BF4ExactSlabStarResidualApproximation.lean:241`.
- `residual_dual_error_identity` and `relativeValue`,
  `lean/YMGap/Continuum/BF4ExactSlabStarVariationalApproximation.lean:84`
  and `:148`.

The approximation index for the returned polynomial test still depends
only on w and epsilon, not extent, late K, link or input polynomial.
The auxiliary conditional-output convergence modulus used in the proof
may depend on input and geometry; it is not the returned approximation
index. No claim of efficient execution of the unreduced rational
iteration is made.

## Actual consumers and limitations

The local finite rational dual value now has an energy-relative error.
Summing those local squared errors introduces no volume factor. This is
useful error control for the prospective defect-retaining collective
certificate; it is not the certificate itself.

In particular, `sum_i ||error_i||^2` is NOT `||sum_i error_i||^2`.
Signed cross terms/overlap still require control. An infinite-degree
positive-form claim is not certified by checking a finite principal
matrix: omitted-mode control is still needed. No useful signed scaling
estimate, physical OS transfer identification, continuum survival, QFT
axioms or every-group mass gap is proved. A03 remains open, so no
canonical chart marker changed and the chart was not reprinted.

Parallel Sol review of the survival branch found no new producer in the
selected-star floor. Its coefficient satisfies
`starRatio(w)<=((1-w)^2)^6` by `starRatio_le_defect_power`,
`lean/YMGap/Continuum/BF4ExactSlabStarVarianceLossObstruction.lean:38`.
Scalar renormalization multiplies norm, loss and response by the same
factor, so does not improve their ratio. The existing relative-loss
consumer remains `dyadic_response_floor_of_relative_energy`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:124`.
Luna independently checked the shift argument and the distinction
between the sum of squared errors and the squared sum.

## Verification

The final focused check ran with one worker and the mandatory 20 GiB
ceiling through the monitored launcher, completing in about 6.6 seconds:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabStarEnergyRelativeApproximation.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabStarEnergyRelativeApproximation.olean
```

All five printed declarations depend only on `{propext, Quot.sound}`.
No new sorry, axiom or analytic premise. No full root build, whole-tree
audit, SDP or large numerical calculation was run. The root import is
registered, but that registration is not a claim of full-root verification.
