# ORIGINAL shared-output heat Laurent interpolation and positive saturation

## Mathematical progress and scope

PROGRESS after `d09afaab7f2e57e9c3b9335c8aeb005786eacd3c`.
The actual finite square and angular-energy interpolants now have their
literal coefficient product/chain Euler identities on the original carrier.
Actual conditional cutoff stability also transports a computed positive
larger prefix to a certificate of the fixed saturated image at strict nomes.
A fixed finite row family has one computed input mode cutoff at every nome.

The whole-project goal remains OPEN: constructive continuum Yang--Mills on
R^4, for every compact simple group, with the required SAME-theory QFT axioms
and positive physical Hamiltonian mass gap. These are local finite SU(2)
identities and positive-map certificates, not an interacting or continuum gap.
No exact displayed chart claim changes; no ASCII reprint.

## 1. Literal finite row calculus

`RatPolyNomeRows` operates on actual lists of pairs `(QPoly.Poly, RatPoly)`.
Nome evaluation scales the original multivariate polynomials; the derivatives
are literal `QPoly.pderiv`, never defined by an intended generator identity.

| declaration | source | result |
| --- | --- | --- |
| `evalRows` | `lean/YMGap/Continuum/RatPolyNomeRows.lean:37` | actual finite polynomial evaluation, all shared variables retained |
| `derivativeRows` | same file:40 | literal coefficient pderiv |
| `mulRows` | same file:43 | complete Cartesian product, actual coefficient pmul |
| `eulerRows` | same file:49 | literal numerator rows `r*N'-E*N` |
| `evalRows_mul` | same file:123 | coefficient-strength product pin |
| `evalRows_derivative_mul` | same file:197 | true formal product rule |
| `evalRows_euler_pin` | same file:223 | actual cleared Euler evaluation |
| `evalRows_euler_mul` | same file:247 | Euler product rule, E allocated to the denominator-bearing factor |
| `evalRows_angularDerivative` | same file:285 | all six actual head fields commute with coefficient evaluation |
| `evalRows_partialHaarHead` | same file:294 | only the original integrated head is removed |
| `evalRows_euler_partialHaarHead` | same file:310 | literal Euler rows commute with partial integration |

## 2. Complete inverse-nome kernel

The common denominator exponent is `E=c4 K`. Every label `spin<=K` has the
actual numerator coefficient
`coeffW w spin * r^(E-c4 spin)`. Dividing by `r^E` gives the ORIGINAL packet
coefficient at `u=w*recip r`. The literal Euler numerator is minus its label
Casimir times that same coefficient. Positive r permits denominator
cancellation; w may be signed, and K=0/spin=0 are included.

| declaration | source | result |
| --- | --- | --- |
| `inverseNomeExponent` | `lean/YMGap/Continuum/SU2QuaternionInverseNomeKernel.lean:42` | computed common power c4 K |
| `inverseNomeRows` | same file:50 | all original characters in inclusive packet order |
| `inverseNomeCoefficient_scaled_eval` | same file:153 | original inverse-nome packet coefficient |
| `inverseNomeCoefficient_euler` | same file:173 | literal per-label Euler derivative |
| `inverseNomeKernel_original_pin` | same file:251 | coefficient-strength full-prefix pin |
| `inverseNomeEuler_chain_pin` | same file:274 | true inverse-nome chain term `-u*formalConditionalKernelDerivative u K` |

No higher labels, output coefficients or spectator variables are dropped.

## 3. Actual inner square and energy curves

Let `V(r)=finiteNomeFlow tail p r`. The checked original identification is
`finiteNomeFlow_original_pin`
(`lean/YMGap/Continuum/SU2QuaternionHeadHeatGenerator.lean:123`): this is the
original head heat whenever its computed input saturation cutoff is retained.
The new inner curves are actual products and rotations of these finite rows.

| declaration | source | result |
| --- | --- | --- |
| `squareNomeRows` | `lean/YMGap/Continuum/SU2QuaternionHeadHeatCurves.lean:60` | actual product of all original flow rows |
| `angularNomeRows` | same file:64 | actual sum of six squared angular row derivatives |
| `squareNomeRows_eval` | same file:76 | coefficient-strength pin to V^2 |
| `angularNomeRows_eval` | same file:81 | coefficient-strength pin to Gamma(V) |
| `formalSquareNomeDerivative_pin` | same file:97 | genuine pderiv gives 2*V*V' |
| `formalAngularNomeDerivative_pin` | same file:113 | genuine pderiv gives 2*mixedGamma(V,V') |
| `finiteNomeFlow_formal_generator` | same file:147 | original input generator r*V'=-L_x V |
| `squareNomeCurve_formal_generator` | same file:156 | r*(V^2)'=-2*V*L_x V under every insertion |
| `angularNomeCurve_formal_generator` | same file:183 | r*Gamma(V)'=-2*mixedGamma(V,L_x V) under every insertion |

The original source may depend on the retained output and every spectator.
The only source guard is support on the original tail+1 blocks. The Laplacian
acts on input x, not output y.

## 4. Original conditional product/chain join

`conditionalLaurentRows`
(`lean/YMGap/Continuum/SU2QuaternionConditionalLaurentRows.lean:40`) multiplies
the complete inverse-nome kernel rows by the same source rows and integrates
only the original head. Its value and Euler data use the original common power.

`conditionalLaurentValue_original_pin` (same file:98) identifies the value
with `C_u[evalRows A r]` at coefficient strength. The actual raw chain split is
`conditionalLaurentEuler_chain_split` (same file:116):

```text
Euler(C_(w/r)[A(r)])
  = -u * formalConditionalNomeDerivative u K A(r)
    + C_u[r*A'(r)],             u=w/r.
```

`conditionalLaurentEuler_input_generator` (same file:185) uses the checked
input-head generator and both integration-by-parts steps to obtain
`C_u[L_x A(r)+r*A'(r)]`, under EVERY surviving insertion. It requires r>0
and tail>0 only; no source support, output independence, saturation or kernel
positivity is supplied as an extra hypothesis to this generic finite identity.

The final functions and formal Euler data are defined in
`lean/YMGap/Continuum/SU2QuaternionHeatLaurentInterpolation.lean:43`
(`squareInterpolation`), :47 (`angularInterpolation`), :51
(`squareInterpolationEuler`) and :55 (`angularInterpolationEuler`).
Their original coefficient-strength value pins are
`squareInterpolation_original_pin` (:67) and
`angularInterpolation_original_pin` (:75).

The proved joins are `squareInterpolation_euler` (:116) and
`angularInterpolation_euler` (:140):

```text
F(r)=C_(w/r)[V(r)^2],       Euler(F)=2*C_(w/r)[Gamma(V(r))]
G(r)=C_(w/r)[Gamma(V(r))],  Euler(G)=2*C_(w/r)[Gamma2(V(r))].
```

Here Euler is literally `r^(-E)*(r*N'(r)-E*N(r))` for the constructed
numerator, not an assumed analytic derivative or a conclusion-defined object.
The square join cancels the actual signed `2*V*L_x V` term. The energy join
uses the actual definition `Gamma2=(1/2)*L_x Gamma-mixedGamma(V,L_x V)`.
Both are all-insertion carrier identities for the SAME retained output,
source and outer K. Independent Sol mathematical reviews passed both the
specializations and the complete implemented generic chain.

## 5. Fixed-row cutoff and actual positive saturation

`rowCutoff` (`lean/YMGap/Continuum/RatPolyNomeRowCutoff.lean:104`) is computed
from actual row evaluation at nome zero. `modeCutoff_evalRows_eq` (:110)
and `rowCutoff_spec` (:127) prove the existing mode cutoff is EXACTLY this
value at every signed nome, for positive block count. Scalar evaluation
does not delete monomials, including zero coefficients. `evalRows_supported`
(:133) inherits the checked support of each fixed base row.

This is not an invariance theorem for harmonic `inputCutoff`, semantic
coefficient-equivalent alternative representations, or changing source rows.
In particular it is not cutoff-, coupling-, width- or spacing-uniform control
of a changing original source. Independent Sol semantic review passed.

`conditionalHeat_cutoff_stable`
(`lean/YMGap/Continuum/SU2QuaternionConditionalHeatSaturation.lean:73`)
proves both actual prefixes above the fixed input's computed mode cutoff
give the SAME conditional image. It uses original-output harmonic
reproduction, not a non-injective substitution into a generic carrier equality.
The nome may be signed; no kernel positivity is assumed.

`positivePrefix`
(`lean/YMGap/Continuum/SU2QuaternionConditionalHeatPositiveSaturation.lean:37`)
computes `max(headCutoff u,K)`. For strict `0<u<1`,
`conditionalHeat_saturated_certificate` (same file:42) extends the existing
concrete two-block heat certificate to tail+1, multiplies by the supported
input certificate and integrates the actual head. The new cutoff equality
then transports that certificate back to the ORIGINAL K-image.
Support and `modeCutoff(tail+1,p)<=K` remain explicit guards.

This does NOT assert that the K-kernel itself is positive, that one positive
prefix works up to nome one, or that positivity survives a changing family.
Nome one still requires particular reproduction. Independent Sol review
passed the certificate extension, support guards and transport direction.

## 6. Backward consumer and honest next join

The actual original Laurent order producer is already checked as
`laurent_monotone`
(`lean/YMGap/Continuum/RationalLaurentIntervalOrder.lean:132`). Its pointwise
Euler sign is not automatically supplied by the carrier identities above.
The next join is the scalar projection of these actual rows under certified
original output weights, its literal Euler pins, Bochner positive-margin
transport and endpoint order for G/r^2 and the square interpolant.
Particular nome-one reproduction must identify the actual squared mean.
Conditional reference angular Poincare and its active-product join are OPEN.

The downstream original-source variance is `projectedReferenceVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:83`),
with checked own-mean cutoff comparison
`projected_variance_cutoff_weighted_le` (same file:133).
Its source is `lastStepProjectedDerivative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean:72`).
The INPUT-gradient energy produced by Poincare is NOT the source-square sum
`projectedDerivativeAngularBudget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`).
Their genuine SAME-source/action/output-weight/surviving-norm estimate is
still needed, retaining both signed Taylor terms. A justified changing-family
signed-window budget and all physical/OS/continuum/QFT/every-group/Clay
obligations remain OPEN. No canonical frontier bundle is inhabited here.

## 7. Exact verification boundary

Eight focused checks passed through `scripts/safe_lean_build.py`, serialized
with one worker, a 20 GiB worker ceiling and 12 GiB reserve. Fresh process,
memory-pressure and swap checks preceded EVERY launch; no competing compiler
was found, free memory remained 76--77%, and swap use was zero.
No full root/full-tree build, full axiom audit or broad guard was run.
Root imports are registration only. Automatic GitHub CI stays manual-only.

| target | accepted log | log SHA256 |
| --- | --- | --- |
| RatPolyNomeRows | `/tmp/ym-nome-rows-20261003-2.log` | `d83b3a6511faa1dd820f6141de181e475a838689c142fa7095628890ac2104e8` |
| SU2QuaternionInverseNomeKernel | `/tmp/ym-inverse-nome-20261003-2.log` | `c6b20934b776501f1154af3e8b19ab4923e90dff86bd3baffc546126c2f8f397` |
| SU2QuaternionHeadHeatCurves | `/tmp/ym-head-heat-curves-20261003-2.log` | `6228dcc360fd9c9306df74c59b8887324bf654302bbd9d994f1e242cadb05928` |
| SU2QuaternionConditionalLaurentRows | `/tmp/ym-conditional-laurent-rows-20261003-1.log` | `673f33e75e26ba08e0752b20b936c544c418f7acadfdc9e52718a333a0b168e3` |
| SU2QuaternionHeatLaurentInterpolation | `/tmp/ym-heat-laurent-interpolation-20261003-1.log` | `d97e2e945534857137a35616d34f2bc10a26f325fd9702734e319792c573eb78` |
| SU2QuaternionConditionalHeatSaturation | `/tmp/ym-conditional-heat-saturation-20261003-1.log` | `e670e5327a106d97c738848ab300882feb59cc1eb74e86676bbc3a1152d5c90c` |
| SU2QuaternionConditionalHeatPositiveSaturation | `/tmp/ym-conditional-heat-positive-saturation-20261003-2.log` | `191107b2b261ba45310fd0259c1879c7af2cf9c270d924aca0e739c64490625b` |
| RatPolyNomeRowCutoff | `/tmp/ym-nome-row-cutoff-20261003-2.log` | `9cc4d93fe501e218cee25d6e3b04935b17939f753eadd1748d83d713d3bc4a0b` |

All 51 printed public gates lie within {propext, Quot.sound}; none has sorryAx
or a classical axiom. No new axiom, native_decide, Mathlib, resource-option
escalation, weakened statement or analytical-bound premise was introduced.
Initial failed checks were local elaboration/namespace repairs; they are not
accepted verification evidence. Parallel Sol/Luna work produced proofs and
reviews; the parent alone ran all serialized compiler checks.

| module under `lean/YMGap/Continuum/` | accepted source SHA256 |
| --- | --- |
| RatPolyNomeRows.lean | `0c5011aed8e670a02de7a3e431e9cf68a46d526023a2c2300cfe896438795e63` |
| SU2QuaternionInverseNomeKernel.lean | `e55cde8cdc59dfd79bd34894b53dfd314e12a557887ad9f4fd23267b6f1bdbed` |
| SU2QuaternionHeadHeatCurves.lean | `14c2b429c2c85ce177c1a730598b68fd50cf182babfb8fad102ec16cadfa1674` |
| SU2QuaternionConditionalLaurentRows.lean | `f8ab503f5747722b5d6db7a1c2f4e9bcd13721ed7703658820b1ce1d07c10f71` |
| SU2QuaternionHeatLaurentInterpolation.lean | `591f6144c35dc468c3d746a93de23828e9c46464d4633706ed23283e72466c0b` |
| SU2QuaternionConditionalHeatSaturation.lean | `aecb71b6e74c22ae91e2d74e31f615920aded42481467fc84a3d9f0e560ca55f` |
| SU2QuaternionConditionalHeatPositiveSaturation.lean | `feecd5a333048509382b6c6546992118b4964a846fef3a8c30d33d439012e2cf` |
| RatPolyNomeRowCutoff.lean | `2acc6f1d05867382d5dd39a3481a249a4316021b8d0f6210643b924173816c22` |
