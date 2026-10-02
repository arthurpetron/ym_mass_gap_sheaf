# Full heat coefficient obstruction to signed transport

The squared-nome affine coefficient shortcut fails beyond the finite-prefix
edge. This report records the checked full-sequence theorem and its exact
scope. The actual interacting Wilson-source estimate remains OPEN.

## Checked original coefficient theorem

`fullCoefficientCutoff`,
`lean/YMGap/Continuum/SU2HeatQuarticFullCoefficientObstruction.lean:100`,
computes the Nat threshold

    J(q,c) = (48 + 6*c.num.toNat)*(1-q).den + 2.

For rational `0<q<1` and `0<=c`, `full_quartic_coefficient_gt` at
`lean/YMGap/Continuum/SU2HeatQuarticFullCoefficientObstruction.lean:267`
proves, for EVERY `j>=J(q,c)`,

    c*coeffW(q*q,j) < quarticCoeff(coeffW(q),j).

The right-hand sequence is the ORIGINAL untruncated `coeffW`, not the
zero-extended `cutCoeff`. The exact five-band compiler is `quarticCoeff`,
`lean/YMGap/Continuum/SU2HeatQuarticFiniteRegroup.lean:31`.
Its positive-spin row is `6*A_j-4*(A_(j-1)+A_(j+1))+A_(j-2)+A_(j+2)`.
The proof uses cleared reciprocal Bernoulli, exact Casimir differences and
positive rational dimension factors. The cutoff and inequalities are
constructed; no asymptotic or tail-smallness premise is supplied.

This is a COEFFICIENT theorem only. It does not yet give an original Haar
negative quadratic, an uncut operator counterexample, a bound or refutation
for the literal interacting Wilson source, or a survival/scaling result.
The positive-source pointwise Haar certificate is unaffected.

## Remaining analytic producer

The target is still the ORIGINAL signed filtered source relative to OWN
interacting variance, together with a lag-one reserve, on a justified family.
The source and backward consumer are already pinned by
`dyadicUnit_filtered_source_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredIncrement.lean:102`, and
`dyadicUnitResponse_filtered_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredSurvival.lean:165`.
No quantitative family input is produced here. Spatial/spacing control,
continuum survival, physical mass calibration, full SAME-theory QFT and
every compact simple group remain OPEN.

## Verification evidence

The final focused check exited zero. Its two public gates report no axioms
for the cutoff and exactly `{propext, Quot.sound}` for the theorem. Independent
source review passed; there are no final errors or warnings. The rejected
first attempt had match-branch indentation errors, repaired only in the new
file without changing its statement or resource limits.

| Artifact | SHA256 |
| --- | --- |
| `SU2HeatQuarticFullCoefficientObstruction.lean` | `6e6df3cc7b9c0238ca19cbfeca069dfe189edfb219c6066ced733fa3885e97a9` |
| `/tmp/ym-quartic-full-coefficient-obstruction-20261002-second.log` | `e22fb99757bc4e835ba6d1fd3264e14ccb6bc3dcab1c5e5e5efe16d02124e939` |

One worker, explicit 20-GiB ceiling and 12-GiB OS reserve were used. Fresh
preflight showed 85 percent pressure-free memory and zero swap. One root
import is registered, NOT aggregate-checked. No broad build/audit, new sorry,
axiom, classical shortcut, weakened field, substituted carrier or CI change.
No exact displayed chart claim changes; its fence is not reprinted.
