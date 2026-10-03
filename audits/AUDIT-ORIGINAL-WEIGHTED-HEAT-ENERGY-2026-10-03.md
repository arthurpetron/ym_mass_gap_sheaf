# ORIGINAL same-output weighted heat-energy estimate

## Mathematical progress and scope

PROGRESS after `4967f141ac2d397000ef6a72a19582d1a3c1ee52`.
For the ORIGINAL finite conditional interpolation
`G(r)=C_(w/r)[Gamma(V(r))]`, the derived bound is
`H[W G(r)] <= r^2 H[W G(1)]` for `0<w<1` and `w<=r<=1`.
The arbitrary original output weight W has a concrete square certificate;
all shared output and spectator dependence stays shared. The derivative
sign and endpoint order are conclusions, not additional analytic premises.

The whole-project goal remains OPEN: nontrivial constructive continuum
Yang--Mills on R^4 for every compact simple group, with the SAME-theory
required QFT axioms and positive physical Hamiltonian mass gap. This local
ordinary conditional heat estimate is not an OS or physical gap.
Exact canonical chart claims do not change; no ASCII reprint.

## 1. Forward: fixed-source original Bochner rows

Support is checked explicitly. `nomeHeatPolynomial_supported`
(`lean/YMGap/Continuum/SU2QuaternionHeadHeatCurveSupport.lean:46`) supplies
support of each actual computed harmonic row. `finiteNomeFlow_supported`
(same file:58) gives support of the computed/padded flow at every signed nome;
it does NOT identify an unsupported incoming polynomial with its padded flow.
The same file proves support preservation of the actual six-plane Laplacian
(:86), angular square (:96), polarized energy (:107), Gamma2 (:119) and
Bochner margin (:130).

`laplacianNomeRows`, `mixedNomeRows`, `energyNomeRows`, `gamma2Rows` and
`bochnerMarginRows` are defined in
`lean/YMGap/Continuum/SU2QuaternionBochnerNomeRows.lean:39`, :42, :46,
:48 and :52. They use all six original head rotations, literal row products,
and the DEFINED `Gamma2=(1/2)L(Gamma)-mixedGamma(p,Lp)`.
No desired Hessian value is substituted for Gamma2.

`evalRows_laplacianNomeRows` (:82), `evalRows_mixedNomeRows` (:89),
`evalRows_gamma2Rows` (:130) and `evalRows_bochnerMarginRows` (:141)
are coefficient-strength pins, preserving shared variables before integration.
`bochnerMarginRows_supported` (:199) checks every fixed row.
`bochnerMarginRows_certificate` (:210) constructs the actual Bochner margin
certificate. `conditional_bochnerMarginRows_certificate` (:218) constructs
positivity of its ORIGINAL saturated conditional image at strict auxiliary
nome `0<u<1`, with computed guard `rowCutoff(tail+1, marginRows)<=K`.
It internally uses a larger positive prefix; it does not assume positivity
of the fixed K-kernel or a prefix uniformly positive up to nome one.

## 2. Exact original weighted scalar polynomial

`weightedNumerator`
(`lean/YMGap/Continuum/QuaternionHaarNomeRows.lean:38`) is a literal finite
QPoly padd/pscale fold of Haar pairings `H[W*row.base]`. Its actual evaluation,
formal derivative, Euler evaluation and Laurent value are pinned by
`weightedNumerator_eval` (:52), `weightedNumerator_derivative_eval` (:88),
`weightedNumerator_euler_eval` (:115) and `weightedNumerator_laurent_pin`
(:140). The weight is the SAME W on every row; no positivity, support or
independence premise is required for these algebraic identities.

`angularNumerator`
(`lean/YMGap/Continuum/SU2QuaternionWeightedHeatInterpolation.lean:62`)
applies that actual fold to the complete original conditional Laurent rows.
`marginCutoff` (:66) computes the cutoff once at nome zero for the fixed
margin skeleton. The checked row-cutoff invariance retains monomials whose
scalar coefficient happens to vanish. It is not uniformity over changing
sources, coupling, volume, width, or lattice spacing.

Let `E=inverseNomeExponent K` and `N=angularNumerator tail w K p W`.
`angularNumerator_original_pin` (:146) proves
`N(r)/r^E = H[W G(r)]`. `angularNumerator_euler_pin` (:154) proves the actual
shifted Euler identity

```text
r^(-E) * (r*N'(r) - (E+2)*N(r))
    = H[W * (angularInterpolationEuler(r) - 2*G(r))].
```

The exponent shift is E+2, not E: the ordered function is G/r^2. N' is
literal QPoly pderiv of the constructed numerator, not defined by its desired
generator expression.

## 3. Backward: genuine scalar endpoint order

`nonnegative_at_left_endpoint`
(`lean/YMGap/Continuum/RationalPolynomialStrictEndpoint.lean:57`) constructs
strict interior mesh points approaching the left endpoint, applies the
literal Taylor budget plus an absolute derivative budget, computes an integer
ceiling, and uses rational Archimedean closure. No continuity axiom or endpoint
sign/order premise is supplied.

`laurent_quadratic_pin`
(`lean/YMGap/Continuum/RationalLaurentQuadraticOrder.lean:69`) proves the exact
positive-power identity `N(r)/r^E = r^2*N(r)/r^(E+2)` for positive r.
`laurent_quadratic_upper` (:113) closes the strict Euler sign at r=w using
the polynomial producer and then applies the original Laurent order theorem.
Signed/zero numerators, E=0 and both endpoints are included. Every reciprocal
cancellation uses a checked positive argument.

## 4. The forward/backward join: proved energy estimate

`angularInterpolation_margin_certificate`
(`lean/YMGap/Continuum/SU2QuaternionWeightedHeatInterpolation.lean:167`)
constructs a certificate of `angularInterpolationEuler-2G` as exactly
`2*C_(w/r)[Gamma2(V)-Gamma(V)]`. The original product/chain generator is
used only after its existing source support guard is checked. At strict
r>w>0 the auxiliary nome satisfies `0<w/r<1`; the fixed source cutoff
allows the constructed saturation certificate from section 1.

Multiplying by ANY certified SAME-output W and taking the original Haar
pairing gives `angularNumerator_euler_nonnegative` (:208).
The actual shifted Euler numerator is nonnegative; no derivative-sign
assumption is introduced. `angularInterpolation_weighted_quadratic` (:220)
then proves the announced bound on the whole closed interval [w,1].
The missing r=w/u=1 sign is closed only as a scalar polynomial sign, not
by a false generic carrier pullback through coordinate identification.

Independent Sol mathematical review passed: source, output weight, shared
spectators, true E+2 shift, reciprocal guards, fixed-skeleton cutoff and
endpoint handling are preserved. No hidden desired analytic premise found.

## 5. Remaining causal joins

OPEN: join the true square Euler identity to the derived energy order to
prove `F(1)-F(w)<=(1-w^2)G(1)`. Identify actual particular endpoints with
`C_w(p^2)`, `(C_w p)^2`, and `C_w Gamma(p)`, then prove conditional reference
angular Poincare and its active-product join.

The downstream source is `lastStepProjectedDerivative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean:72`).
Its INPUT-gradient energy is NOT the source-square sum named
`projectedDerivativeAngularBudget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`).
Their genuine SAME-source/action/output-weight/surviving-norm estimate,
both signed Taylor terms, and a justified changing-family signed-window
bound remain unpaid. Physical/OS/scaling/continuum/QFT/every-group/Clay
remain OPEN. No canonical frontier bundle is inhabited by this increment.

## 6. Exact verification boundary

Six final focused checks passed, serialized through safe_lean_build.py with
one worker, 20 GiB worker ceiling and 12 GiB reserve. Fresh process/swap/
memory-pressure checks preceded EVERY launch; no competing compiler was
found, free memory remained 76--77%, and swap use was zero. Parent alone
ran the compiler; Sol/Luna produced proofs, review and metadata in parallel.
All 34 printed gates are within {propext, Quot.sound}, with no sorryAx.
The Bochner-row check has four unused-variable warnings (i,j at lines 182
and 188); the other five accepted logs are warning-free. Earlier failed
checks were local namespace/parser repairs, not accepted proof evidence.
No new sorry/axiom, classical shortcut, Mathlib, native_decide, resource-option
escalation, analytic-bound premise, full root/tree build, broad guard or
full axiom audit is claimed. Root imports are registration only; GitHub CI
remains manual-only.

| target | accepted log under `/tmp/` | log SHA256 |
| --- | --- | --- |
| QuaternionHaarNomeRows | `ym-quaternion-haar-nome-rows-20261003-1.log` | `e2388de31a15c2ea97c027808a5c643d488a56efe868f1636d82723487eb24ab` |
| SU2QuaternionHeadHeatCurveSupport | `ym-head-heat-curve-support-20261003-3.log` | `a020c03d9bd09a73a047434f13ac864f937a1041abfe87588444820f9e2d00e4` |
| RationalPolynomialStrictEndpoint | `ym-rational-polynomial-strict-endpoint-20261003-1.log` | `83a86f1b10df0d5c47b3ea85980d9465ed42bcaa23ecd18fae359a0587303054` |
| SU2QuaternionBochnerNomeRows | `ym-su2-bochner-nome-rows-20261003-1.log` | `1a68098a89d9503cabe19b1a78a5db3c6ec1eca4772fe55deef7852cd5fd346d` |
| RationalLaurentQuadraticOrder | `ym-rational-laurent-quadratic-order-20261003-1.log` | `30e36df4eb2d5c8f66a59481c560a1a57295c88f062620a4b80ee54426f89bd9` |
| SU2QuaternionWeightedHeatInterpolation | `ym-su2-weighted-heat-interpolation-20261003-2.log` | `5574d80bcd41005c1d7db8804076f1a826e6eabd4d8a5dd440cb7103904c12a3` |

| source under `lean/YMGap/Continuum/` | accepted SHA256 |
| --- | --- |
| QuaternionHaarNomeRows.lean | `ca9fb648d3bc7ef2394bd463dc2b1e2d696992fe6fec97505c1782d6cfbb2d5b` |
| SU2QuaternionHeadHeatCurveSupport.lean | `59223f617e484a661a534a3a8b51c8920f87f71bd2069b254c2521b69d06c536` |
| RationalPolynomialStrictEndpoint.lean | `1486cc25bec90e89e20a7c3c8637ae719973c68d389444ecd51bd56bfe4f9b92` |
| SU2QuaternionBochnerNomeRows.lean | `74f0af1710d0631e1d18cf3d67e3e82ff61c9fe6489691c6ac36f9ea9b578aae` |
| RationalLaurentQuadraticOrder.lean | `643ef5915355bdd32359a2ca1051f275b955dc7c3bdbe4d9b7a644d6593d1e2d` |
| SU2QuaternionWeightedHeatInterpolation.lean | `7ba88cbe66d10f6a306d6fd29773e12ed82b8075a86300ec3a44f202bc93f2c7` |
