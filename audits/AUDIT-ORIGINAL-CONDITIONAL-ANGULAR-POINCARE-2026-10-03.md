# ORIGINAL one-link conditional angular Poincare inequality

## Mathematical progress and scope

PROGRESS after `151fd81`: the one-link bound is now derived,

```text
H[W*(C_w(p^2)-(C_w p)^2)] <= (1-w^2)*H[W*C_w(Gamma(p))].
```

Here C_w is the ORIGINAL finite relative conditional heat at cutoff K,
integrating the original head x to the already-existing output y. p(x,y,z)
may depend arbitrarily on that output and all spectators; W(y,z) is any
already-constructed square-certificate weight, including zero. Source
support, tail>0, 0<w<1, and a computed fixed-source cutoff remain explicit.
No variance estimate, derivative ceiling, independence or physical-gap
premise is supplied. The true Euler ceiling is derived inside the proof.

The whole-project target remains OPEN: nontrivial constructive continuum
Yang--Mills on R^4 for EVERY compact simple group, SAME-theory required QFT
axioms, isolated vacuum and finite positive physical Hamiltonian mass gap.
This ordinary one-link reference heat variance is not an interacting or OS
gap, continuum survival, physical calibration or Clay closure. Exact canonical
chart claims are unchanged; no ASCII reprint.

## 1. Forward: actual original endpoints

`finiteNomeFlow_one_carrier`
(`lean/YMGap/Continuum/SU2QuaternionHeatInterpolationEndpoints.lean:104`)
uses the actual source-computed input cutoff and proved headMap reproduction
to identify V(1) with p under EVERY same-carrier insertion.
`squareInterpolation_one` (:112) and `angularInterpolation_one` (:126)
give F(1)=C_w(p^2) and G(1)=C_w Gamma(p). The angular transport uses proved
derivation/carrier compatibility, not an output-independence assumption.

`interpolationEndpointCutoff` (:140) computes
`max(inputCutoff, max(rowCutoff(flowRows), rowCutoff(squareRows)))`.
`squareInterpolation_left_endpoint` (:148) proves F(w)=(C_w p)^2.
It separately applies PARTICULAR supported-source conditional nome-one
reproduction to the actual square rows and V(w). The only diagonal
substitution transport is the actual COEFFICIENT pin to V^2 and the proved
product rule for substituteRetained. Direct composition at the already-existing
output identifies C_1(V(w)) with C_w p. No generic Haar-carrier equality is
pulled through non-injective identification of coordinates.

## 2. Backward: constructive square increment

`laurent_quadratic_increment`
(`lean/YMGap/Continuum/RationalLaurentQuadraticIncrement.lean:146`) uses the
literal comparison polynomial `c*r^(E+2)-N`. Its genuine formal derivative
and positive-coordinate denominator cancellation produce the Euler sign
for this comparison from the actual normalized Euler ceiling. Existing
constructive Laurent order then proves
`F(1)-F(w)<=(1-w^2)*c`. Signed/zero N,c and E=0 are included; no integration
axiom or desired endpoint order is assumed. This generic producer's Euler
premise is supplied from proved original heat identities in section 3.

## 3. The SAME-source forward/backward join

`squareNumerator`
(`lean/YMGap/Continuum/SU2QuaternionConditionalAngularPoincare.lean:51`) is
the literal weighted coefficient fold of the ORIGINAL conditional square
rows. `squareNumerator_original_pin` (:63) identifies its Laurent evaluation
with H[W F(r)], at every rational r.

`squareNumerator_euler_energy` (:72) proves its ACTUAL normalized Euler
derivative is 2*H[W G(r)], using literal pderiv and the previously checked
square product/chain generator. `squareInterpolation_weighted_increment`
(:96) supplies the scalar increment producer's ceiling from the DERIVED
energy order `angularInterpolation_weighted_quadratic`
(`lean/YMGap/Continuum/SU2QuaternionWeightedHeatInterpolation.lean:220`).
The SAME W,p,K stay fixed; no desired derivative ceiling is added to the
public heat theorem's hypotheses.

`poincareCutoff` (:55) is exactly
`max(marginCutoff, interpolationEndpointCutoff)` for this fixed source.
`heatVariance` (:59) is the actual own-mean polynomial
`C_w(p^2)-(C_w p)^2`. The final theorem
`conditionalHeat_weighted_angular_variance` (:132) combines the increment,
true square/mean-square endpoints and original input-gradient endpoint to
prove the stated inequality under arbitrary certified W.

Independent Sol read-only mathematical review passed: literal derivative,
weight, source, cutoff, signed scalar increment and all endpoint pins agree.
There is no hidden desired variance premise, output independence, diagonal
Haar-equality pullback or substitution of source square for input-gradient
energy. The certificate weight may be zero; no mass or norm is inverted.

## 4. Remaining causal frontier

OPEN: active-product reference Poincare for the complete original source,
with selected-link reindexing, own-mean variance telescoping and positive
remaining conditional kernels under the SAME output weight. This one-link
theorem does not itself discharge the full product reference variance.

The downstream object is `projectedReferenceVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:83`),
with original source `lastStepProjectedDerivative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean:72`).
The ORIGINAL K-source/action/transfer stay fixed while its auxiliary reference
kernel uses L. `projected_variance_cutoff_weighted_le`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVarianceCutoff.lean:133`)
already supplies the near-unit cutoff comparison.

INPUT-gradient energy of the complete Q_K is NOT the Q_K^2 sum named
`projectedDerivativeAngularBudget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean:146`).
Their genuine SAME-source/action/output-weight/surviving-norm estimate,
both signed Taylor terms and a justified changing-family signed-window
budget remain OPEN, together with physical/OS/scaling/continuum/QFT/every-group/
Clay requirements. No canonical frontier bundle is inhabited by this increment.

## 5. Exact verification boundary

Three final focused checks passed through safe_lean_build.py, serialized with
one worker, a 20 GiB worker ceiling and 12 GiB reserve. Fresh process/swap/
memory-pressure checks preceded EVERY launch; no competing compiler was
found, free memory stayed 76--77%, and swap use was zero. Parent alone ran
the compiler; parallel Sol proof construction/review did not launch builds.
All 13 printed gates lie within {propext, Quot.sound}, without warnings or
sorryAx. Earlier failed checks were only parser/implicit-index repairs and
are not accepted evidence. No new sorry/axiom, classical shortcut, Mathlib,
native_decide, weakened statement or resource-option escalation was introduced.
No full root/tree build, full axiom audit, broad guard or progress-metric run
is claimed; root imports are registration only. CI remains manual-only.

| target | accepted log under `/tmp/` | log SHA256 |
| --- | --- | --- |
| RationalLaurentQuadraticIncrement | `ym-rational-laurent-quadratic-increment-20261003-2.log` | `54669d467836c50755058331c0dd9a895700a42766c279f9d5e4ca73b6f061ce` |
| SU2QuaternionHeatInterpolationEndpoints | `ym-su2-heat-interpolation-endpoints-20261003-1.log` | `1a26b53c26d66f68b1a710ad8fd67021c694caeeb445de1cecc6c7e694d3504b` |
| SU2QuaternionConditionalAngularPoincare | `ym-su2-conditional-angular-poincare-20261003-2.log` | `1ede89fac3e1ee48f29d4a52a3dc04e27844136d9759431e8485e839b5db0e7f` |

| source under `lean/YMGap/Continuum/` | accepted SHA256 |
| --- | --- |
| RationalLaurentQuadraticIncrement.lean | `92cfed22d64cdb893e0c16f6c7aaa579b0cbbdf2cb48ee360ed4b2d3f9706000` |
| SU2QuaternionHeatInterpolationEndpoints.lean | `c1f362ffc4e9fcf9e56a9aba37783954eefd7ca5457a46286f20b85406191d2d` |
| SU2QuaternionConditionalAngularPoincare.lean | `3af85d13f74d40bd95397515982059a254570bb0142141ba9b509f6760771b56` |
