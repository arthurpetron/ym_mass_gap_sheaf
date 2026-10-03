# ORIGINAL conditional input generator and constructive Laurent endpoint order

## Mathematical progress and scope

PROGRESS after `255a3fb6dee432a7978e06f9dc065acfac059aa6`:
finite signed rational functions now have constructive endpoint order from
their literal cleared formal derivative sign and an explicit positive
denominator floor. Specialization proves order of the ORIGINAL Laurent
function `eval p x / x^E` on `[a,b]` contained in `[w,1]`, for `w>0`.
The numerator may be signed or zero; exponent zero and equal endpoints are
included. No endpoint-order premise or denominator-multiplied FUNCTION is
substituted for the requested conclusion.

From the forward end, literal original packet coefficient differentiation
and two angular integration-by-parts steps prove the actual conditional
INPUT generator `u*partial_u C_u[p]=-C_u[L_x p]`, preserving arbitrary
retained-link and shared spectator coefficients.

The whole-project Clay target remains OPEN: nontrivial continuum Yang--Mills
on R^4 for every compact simple group, with the required SAME-theory QFT
axioms and positive physical Hamiltonian mass gap. This finite calculus
producer is a backward prerequisite, not a conditional heat variance,
interacting/scaling estimate, physical mass or continuum construction.
Canonical chart claims are unchanged; no ASCII reprint.

## 1. Explicit signed Taylor cell

Declarations in `lean/YMGap/Continuum/RationalPolynomialTaylorCell.lean`:

| declaration | line | actual result |
| --- | --- | --- |
| `primitiveCellBudget` | 45 | computed degree-weighted absolute coefficient sum |
| `primitiveCellBudget_nonnegative` | 49 | nonnegativity of that data |
| `power_cell_difference_le` | 57 | unit-interval power difference bounded by degree times cell width |
| `monomial_cell_error` | 77 | exact primitive minus left rectangle bounded by degree times width squared |
| `primitive_cell_error` | 108 | signed primitive remainder controlled by its computed coefficient budget |
| `taylorCellBudget` | 157 | actual budget of the literal coefficient derivative |
| `taylorCellBudget_nonnegative` | 159 | nonnegativity of this budget |
| `polynomial_taylor_cell_error` | 164 | absolute first-order Taylor error of actual Horner evaluation bounded by width squared times the budget |

For `delta=y-x` and `0<=x<=y<=1`, the last theorem proves
`abs(p(y)-p(x)-delta*p'(x)) <= delta^2*taylorCellBudget p`.
The prime means literal `QPoly.pderiv`, not an assumed analytic derivative.

## 2. ORIGINAL quotient order

Declarations in `lean/YMGap/Continuum/RationalFunctionIntervalOrder.lean`:

| declaration | line | actual result/data |
| --- | --- | --- |
| `quotient` | 32 | actual numerator evaluation times total reciprocal of denominator evaluation |
| `derivativeNumerator` | 35 | literal polynomial `q*pderiv p - p*pderiv q` |
| `derivativeNumerator_eval` | 38 | exact cleared quotient-rule evaluation |
| `quotient_denominator_pin` | 45 | ratio times denominator equals numerator on the positive-denominator domain |
| `cellBudget` | 54 | BOTH signed Taylor errors, capped by actual weighted coefficient norms |
| `cellBudget_nonnegative` | 57 | nonnegativity of this data |
| `cellConstant` | 63 | computed cell budget divided by the SQUARE of visible floor d |
| `cellConstant_nonnegative` | 65 | nonnegativity of this data |
| `quotient_cell_le` | 108 | genuine quotient cell order up to the explicit quadratic error |
| `quotient_monotone` | 218 | endpoint order of the original quotient from pointwise formal derivative sign and d>0 with d<=q(x) |

The finite identity, with both signed remainders retained, is

```text
qx*py-qy*px
  = delta*(qx*p'x-px*q'x) + qx*Rp-px*Rq.
```

The positive floor gives `qx*qy>=d^2`; no numerator, norm or variance is
inverted. The actual quotient difference is bounded by
`delta^2*cellConstant p q d`. On an explicit N+1-cell mesh, the accumulated
error is at most `cellConstant/(N+1)`, since the interval length is at most
one. A computed natural ceiling and constructive rational Archimedean
closure remove the error. This orders `p/q` itself.

Seven EXISTING grid lemmas in
`lean/YMGap/Continuum/RationalPolynomialIntervalOrder.lean` are exposed with
unchanged proof bodies: `node_zero:209`, `node_endpoint:214`, `node_step:226`,
`mesh_nonnegative:238`, `node_mono:242`, `node_in_interval:247`, and
`mesh_le_inverse:254`. They are used by the quotient proof, not new aliases
or new mathematical claims.

## 3. Actual Laurent denominator and Euler sign

Declarations in `lean/YMGap/Continuum/RationalLaurentIntervalOrder.lean`:

| declaration | line | actual result/data |
| --- | --- | --- |
| `laurent` | 33 | literal `eval p x * recip(RGTransport.qpow x E)` |
| `coordinatePower_eval` | 42 | actual polynomial denominator equals the project's right-fold power, including E=0 |
| `laurent_quotient_pin` | 72 | exact pin to that polynomial quotient at positive x |
| `euler_derivativeNumerator_pin` | 93 | `x*D(p,x^E)=x^E*(x*p'(x)-E*p(x))`, without x>0 or E>0 |
| `laurent_monotone` | 132 | ORIGINAL Laurent endpoint order from the Euler numerator's pointwise sign on [a,b] |

For positive x the cleared Euler identity gives the actual quotient
derivative sign. The denominator floor is COMPUTED as `w^E`, not assumed
as an opaque constant. Positive x is cancelled only in the derivative
sign; the function itself is never replaced by `x^E*laurent p E x`.
Independent Sol source/mathematical review passed the Taylor orientation,
floor, mesh closure, Euler sign and signed/zero/degree-zero cases.

## 4. Forward: ORIGINAL conditional INPUT generator

Declarations in `lean/YMGap/Continuum/SU2QuaternionConditionalHeatGenerator.lean`:

| declaration | line | actual result/data |
| --- | --- | --- |
| `nomeCoefficient` | 60 | literal dimension times coordinate power for the original spin label |
| `conditionalHeatNomePolynomial` | 64 | all original coefficient/character rows through the inclusive cutoff |
| `finiteConditionalKernel` | 67 | evaluation of those literal coefficients against the original relative characters |
| `formalConditionalKernelDerivative` | 72 | literal coefficient pderiv, NOT a Casimir-defined derivative |
| `finiteConditionalHeat` | 76 | partial integration of that actual kernel against arbitrary p(x,y,z) |
| `formalConditionalNomeDerivative` | 80 | partial integration of the literal kernel coefficient derivative |
| `finiteConditionalKernel_original_pin` | 103 | coefficient-strength pin to the ORIGINAL relative heat packet |
| `finiteConditionalHeat_original_pin` | 122 | coefficient-strength pin to ORIGINAL conditionalHeat |
| `conditionalKernel_formal_nome_generator` | 185 | literal finite kernel Euler derivative equals minus its INPUT Laplacian |
| `conditionalHeat_formal_nome_generator` | 297 | input generator identity under EVERY surviving insertion, with only tail>0 |

Every finite cutoff, including zero, and every rational nome are included.
No source support, saturation, positivity, independence or inverse is a
premise. Kernel Casimir eigenvalues supply the negative input Laplacian;
two actual Haar angular integration-by-parts identities move it onto p.
Only the LIFTED TEST BOUNDARY is head-independent; p itself is arbitrary.
The existing retained y and every z spectator survive. An output-Laplacian
formula would differentiate y-dependent coefficients and is NOT asserted.
Independent Sol source/mathematical review passed this finite input pin.

## 5. Actual consumer and remaining joins

The next forward objects are the original shared-output heat interpolants
`F(r)=C_(w/r)((P_r Q)^2)` and `G(r)=C_(w/r)(Gamma(P_r Q))`.
Their exact finite Laurent rows and literal formal derivative pins still
must be constructed. The original-head generator is checked in
`SU2QuaternionHeadHeatGenerator.headMap_formal_nome_generator`
(`lean/YMGap/Continuum/SU2QuaternionHeadHeatGenerator.lean:199`). The outer
conditional input generator is now proved in section 4. The actual
Laurent-row PRODUCT/CHAIN derivative pins for F,G are still missing;
separate inner/outer generators do not assert those joins automatically.

Strict intermediate nomes require computed larger positive prefixes and
saturation; nome one uses particular reproduction. Actual derivative
signs must be proved before `laurent_monotone` applies. Conditional
Poincare, its active-product/tensorization join, and the useful original
signed-window scaling budget remain OPEN.

The current backward consumer is `projectedReferenceVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:83`),
which retains the full ORIGINAL K-source and changes only the auxiliary
kinetic kernel to L. Its constructed own-mean cutoff comparison is
`projected_variance_cutoff_weighted_le` (same file:133).
The source is `lastStepProjectedDerivative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean:64`),
the fringe average of the COMPLETE signed incoming derivative.

Important additional join: `projectedDerivativeAngularBudget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`)
sums that source's SQUARE, not its INPUT-gradient energy. A conditional
Poincare estimate produces the latter; these are NOT automatically the
same budget. It still needs a genuine estimate preserving the original
action, output weights, signed Taylor terms and surviving norm.
For a FIXED certified derivative-square insertion, the pure L-to-K kernel
comparison is already supplied by reversing K,L in
`SU2QuaternionProductHeatRelativeCutoff.productHeat_relative_upperCertificate`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatRelativeCutoff.lean:329`).
This does not pay the missing derivative-energy/surviving-norm estimate.

## 6. Exact focused verification

Five serialized monitored checks passed, with fresh process, pressure and
swap inspection before every launch. Every command used
`scripts/safe_lean_build.py --jobs 1 --reserve-gib 12
--check-worker-limit-gib 20 --status-seconds 300 --check ... --check-output ...`.
No full root/full-tree build, full axiom audit or broad guard was run.

| target | accepted log | log SHA256 |
| --- | --- | --- |
| RationalPolynomialIntervalOrder | `/tmp/ym-rational-polynomial-interval-mesh-20261003-1.log` | `e27cd8a68ea18eceeff0f20753cf5755bce024df0a74caed511a0f8bcf3a9929` |
| RationalPolynomialTaylorCell | `/tmp/ym-rational-polynomial-taylor-cell-20261003-3.log` | `9bcbacab1a048048cb6c320bd3a9e5a2494985f5d6cf532487ed674aed373934` |
| RationalFunctionIntervalOrder | `/tmp/ym-rational-function-interval-order-20261003-1.log` | `d0746327c841c98dc32ad1608a22c5550641dbc709dcfb719c851a8cb3edfce6` |
| RationalLaurentIntervalOrder | `/tmp/ym-rational-laurent-interval-order-20261003-2.log` | `7fde20a8fded03a8e501c39a15442d5740d0c62f2f727169d92ae654d8983e27` |
| SU2QuaternionConditionalHeatGenerator | `/tmp/ym-conditional-heat-generator-20261003-1.log` | `43e81f46f4908198608f9242fee25b5eafe5782ac72bea85f904e0e7b778e0d7` |

All 55 printed public gates lie within {propext, Quot.sound}: 33 gates
in the four new modules, seven newly exposed existing grid gates, and
15 unchanged existing interval-order gates. No sorryAx, Classical.choice,
new axiom, native_decide or resource-option escalation occurs in the
accepted sources/gate output. Failed checks were ordinary elaboration
repairs (let-atom reflection, match layout, namespace ambiguity); no
mathematical statement or safety limit was weakened.

| module under `lean/YMGap/Continuum/` | accepted source SHA256 |
| --- | --- |
| `RationalPolynomialIntervalOrder.lean` | `19966ace3508b0ef6713c7c92594965e296b688a7c6612106d3b2a619ac6d56b` |
| `RationalPolynomialTaylorCell.lean` | `f3ccc8f440aeadc58574fbfe9bdba65ce6b555ad383cd0b5d32b9bb30b0bd77c` |
| `RationalFunctionIntervalOrder.lean` | `031962d6cdaca67c927b1889efca2b7b39b347952e60dbf7b77ff21022157473` |
| `RationalLaurentIntervalOrder.lean` | `2f969ca9d5cd29f6c87ddfc175e2138e52e19b6fce4a0bc3b757222ce187694e` |
| `SU2QuaternionConditionalHeatGenerator.lean` | `0eaf95a9f1aef2fc5f662bc03f4e1a14e409ebe286103dedc87cb5f3fa865f9a` |

Root imports are registration only. No frontier bundle, scorecard atom,
canonical displayed claim or Clay obligation is claimed discharged.
