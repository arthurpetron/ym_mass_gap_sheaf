# Witnessed real scalars and a normalized excitation on the same union

Date: 2026-09-16. Base checkpoint: `d18fd1d`, committed and pushed before
this increment. The preceding positive-response goal turn is **PROGRESS**.

## Whole-project goal and precise result

For every compact simple gauge group, construct a nontrivial continuum
Yang--Mills theory on R^4 with the required QFT axioms, isolated vacuum and
positive physical Hamiltonian mass gap. Keep constructive witnesses/moduli,
the Mathlib-free MLTT/HoTT axiom gate, and SAME physical objects throughout.
**The continuum/all-group Clay target remains OPEN.**

This increment constructs real scaling on the EXISTING `UnionCompletion`
for a supplied `CReal` together with its `QCauchy` data. Applying that action
to the original excitation gives an actual unit-norm vector in the original
unit complement with a witnessed rational interval

`0 < responseFloor/P <= B(v,T_2 v) <= twoStepRate(nome) < 1`.

Here `P` is a computed upper bound for the ORIGINAL unnormalized squared norm,
not its square root. Nome is fixed to `1/1024` for the normalized instance.
The transfer is the original physical two-lattice-step time map. No eigenvector,
continuous-time Hamiltonian, physical mass, or canonical OS-root inhabitant
is asserted.

## Actual scalar construction and modulus

`BF4SpatialUnionScalarDistance.distSq_scalar_difference`,
`lean/YMGap/Continuum/BF4SpatialUnionScalarDistance.lean:61`, proves that
changing rational coefficients `a,b` on the same stage costs exactly
`(a-b)^2` times its actual squared norm. `scalar_change_bound` (:74) applies
the existing explicit coefficient tolerance and spends `epsilon/4`.

`BF4SpatialUnionRealScalarCauchy.realScalarCauchy`,
`lean/YMGap/Continuum/BF4SpatialUnionRealScalarCauchy.lean:123`, has literal
sequence `smulStage (s.approx n) (X.seq n)`. `realScalarRate` (:56) takes the
maximum of two computed tail anchors and the supplied scalar/vector rates:

- scalar anchor `cs.M 1` and original vector `normBase`;
- vector modulus at `scalarTolerance (scalarCeiling s cs) (epsilon/4)`;
- scalar modulus at `coefficientTolerance (normCeiling PD X) epsilon`.

The second tolerance also carries the proved nonnegative norm-ceiling witness.
`realScalar_bound` (:64) splits the difference into a vector-change leg and a
scalar-change leg. Each costs `epsilon/4`; the existing squared-distance
triangle doubles each and gives `epsilon`. The rate stays in `Type` and no
modulus is extracted from legacy `CReal.cauchy` propositional existence.
The construction permits original stage streams with growing support bases.

`BF4SpatialUnionCompletedRealScalar.representativeInner_realScalar_left`,
`lean/YMGap/Continuum/BF4SpatialUnionCompletedRealScalar.lean:45`, identifies
the mixed pairing limit using the actual dense homogeneity. Pairing separation
proves scalar/vector/modulus independence in `realScalarCauchy_congr` (:64).
`completedRealSmul` (:74) descends by `Quotient.lift`, not representative
selection. Both pairing homogeneities are at :84 and :90; rational scaling is
recovered by `completedRealSmul_ofQ'` (:103).

`BF4SpatialUnionRealScalarAlgebra.completedRealSmul_addScalar` and
`completedRealSmul_mul`,
`lean/YMGap/Continuum/BF4SpatialUnionRealScalarAlgebra.lean:45` and :56,
use the existing computed scalar sum/product Cauchy data. Negation,
subtraction, orthogonality and quadratic distance scaling are proved in the
same module. `completedTime_realSmul` (:99) commutes the original physical
time with the actual action; `completedDist_realSmul` (:107) keeps the
existing squared distance.

This is NOT an assertion that every bare legacy `RC` value has a chosen
computational modulus. The supplied-scalar interface is explicit in each
declaration and fully instantiated by the normalization below.

## Original operator identities, not replacement constructions

`BF4SpatialUnionRealLinearOperators.scalarUnitCauchy_eq_realSmul`,
`lean/YMGap/Continuum/BF4SpatialUnionRealLinearOperators.lean:58`, identifies
the earlier specialized unit-multiple construction with the new action.
`unitProjection_mk_as_realSmul` (:65) retains exactly the old computed
`unitCoefficient` and `unitCoefficientCauchy`.

The existing projection, centering, defect `Id-T_2` and reduced inverse are
homogeneous for the supplied real scalars: `unitProjection_realSmul` (:73),
`center_realSmul` (:78), `defect_realSmul` (:83), and `resolvent_realSmul`
(:88). The proof tests against the actual pairing and uses the operators'
already proved self-adjointness. No extra continuity or spectral premise is
introduced, and no new operator is substituted for the original one.

## Normalize the actual excitation and preserve its response

`BF4SpatialUnionNormalizedExcitation.normCeiling`,
`lean/YMGap/Continuum/BF4SpatialUnionNormalizedExcitation.lean:64`, is the
existing spatial `positivePrefactor` at base one and radius zero.
`originalNorm_ceiling` (:78) first pins the excitation norm to its exact
lag-zero centered moment and then applies the existing geometric bound at
lag zero. It does not evaluate a potentially huge Cauchy sample or use an
old carrier's norm. `originalNorm_floor` (:71) is the actual local-star floor.

`normalizer` (:88) and `normalizerCauchy` (:91) use the generic constructive
clamped inverse-square-root construction on that ORIGINAL norm and its
QCauchy data. The new `unitExcitation` (:96) belongs to the existing unit
complement; `unitExcitation_norm` (:105) proves its squared norm is exactly one.

`normalizedResponse` (:123) is the actual original lag-two centered scalar
multiplied twice by the normalization real. Its explicit QCauchy data are
returned at :125. `normalizedResponse_pin` (:129) identifies it with
`B(unitExcitation,T_2 unitExcitation)` by original time commutation and the
existing excitation correlator pin.

The rational lower bound is `rayleighFloor=responseFloor/P` (:136), positive
by :138. `normalizedResponse_floor` (:146) uses the full recently proved
positive response and the actual norm ceiling. The upper endpoint is
`rayleighCeiling=twoStepRate nome hd` (:141), strictly below one by :143.
`normalizedResponse_ceiling` (:152) applies the existing universal completed
strict form bound to this exact unit vector.

`normalizedCertificate` (:160) returns the vector, both rational endpoints,
response `CReal`, explicit `QCauchy`, exact norm and operator pin, and both
inequalities as Type-valued data. It does not merely assert existence in Prop.

## Remaining causal joins

`CanonicalOSRoot.PositiveTimeOSRoot`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, still demands rational-valued
`GNSData` at :272, actual supported-observable representation at :290, and
essential surjectivity at :296. Its normalized-probe/response fields (:321,
:330) are not inhabited by this RC-valued union theorem. Normalization alone
does not provide these missing physical maps or resolve the scalar interface.
No canonical frontier field or scorecard was weakened or declared closed.

Full signed/axiswise spatial symmetry, original observable coverage and
full Hilbert/OS/QFT identification remain open. No arbitrary quotient-sequence
completeness is asserted. The already proved union Cauchy--Schwarz and
represented-row limits are prerequisites, not new open tasks to duplicate.
Changing-scale original-action estimates outside the obstructed small-nome
AF chart, actual physical time/spacing and mass calibration, continuum
survival, and every compact simple group's physical producers remain open.

## Verification and parallel review

All six modules passed on their first focused check through
`scripts/safe_lean_build.py`, one worker/20 GiB, with fresh process/swap
preflight before each run. All 56 public printed gates depend only on
`{propext, Quot.sound}`. Final logs contain no errors, warnings, `sorryAx`,
classical dependency or native decision axiom.

| Module under `lean/YMGap/Continuum/` | Gates | Log under `/tmp/` | SHA-256 |
| --- | ---: | --- | --- |
| BF4SpatialUnionScalarDistance | 2 | `ym-union-scalar-distance-20260916.log` | `2bcb3e3a794cb1d64f6d29c17f2252ee61a718f14bc95e353e871df790e19cf6` |
| BF4SpatialUnionRealScalarCauchy | 5 | `ym-union-real-scalar-cauchy-20260916.log` | `0a4ba6ee2f78db122abbe4a739df0eba5df4cc821de312a0db164fa79816ed96` |
| BF4SpatialUnionCompletedRealScalar | 12 | `ym-union-completed-real-scalar-20260916.log` | `7122f8493eeaff061cf1fd59ce6c7912e334f2b75109262ed258d397714abba8` |
| BF4SpatialUnionRealScalarAlgebra | 9 | `ym-union-real-scalar-algebra-20260916.log` | `0905354d8a9bafecc7ba01435cae58038f1866e05b05763addc517c1bb0d1bd8` |
| BF4SpatialUnionRealLinearOperators | 6 | `ym-union-real-linear-operators-20260916.log` | `a4d9ee0e278f3fa06ebd0e34b0ab7530aa4463c67a95c33b03e25c82560bc8f2` |
| BF4SpatialUnionNormalizedExcitation | 22 | `ym-union-normalized-excitation-20260916.log` | `5fbfae49d058da08956deeeb68eea15f3a03973acc34fcf0d40b42273cac71a2` |

Parent plus three agents worked in parallel on the dense scalar estimate,
actual Cauchy/quotient construction, scalar laws and normalized physical
instance. Independent source review covered the explicit rates, original
norm and time pins, division by the squared-norm ceiling, and original
operator identities. Only the parent compiled, with no overlapping builds.
No old Lean proof, sorry, axiom, analytic guard, canonical field or safety
limit changed. Root imports were added; root/full-tree/full axiom audit and
guards were not run. CI remains manual-only; no literature scan occurred.
