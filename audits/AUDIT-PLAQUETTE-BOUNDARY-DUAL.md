# Original-action signed plaquette boundary duals

Date: 2026-09-17 UTC. Parent checkpoint: `bdf2268`.

## Whole-project goal and preserved results

Construct a nontrivial continuum Yang--Mills theory on R^4 for every compact
simple gauge group, satisfying the required QFT axioms and possessing a
positive physical Hamiltonian mass gap. Keep the same theory throughout the
construction, with constructive witnesses and the repository's Lean axiom
gate. The full goal remains OPEN.

The small-nome fixed-spacing branch already has a completed Wilson
vacuum-complement gap and a normalized nonzero excitation:
`completed_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionCompletedGap.lean:153`, and
`normalizedCertificate`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean:165`.
This increment addresses original-action estimates beyond that branch's
small-nome guards, not a missing completion of the proved branch.

## Mathematical change: coefficient detection without a common private link

For a selected original action A and physical plaquette p, let S_p consist
of ALL selected heat factors touching ANY of p's boundary links. Let R_p
contain exactly the remaining factors. The coefficient identity A=S_p*R_p
is `selected_heat_partition`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryErasure.lean:115`.
The star contains at most 24 factors under the explicit physical-membership
and nodup assumptions: `boundaryStar_length_le_twentyFour`, same file `:93`.
The rest misses every boundary link of p: `rest_misses`, `:130`.

For each distinct other plaquette q, `missingLink` (`:157`) constructs a
boundary link of p absent from q. The link can differ for each q. Thus no
single private link is required for a closed or shared-link plaquette family.
Exact original quaternion character selection gives

```
H[R_p*chi_p*chi_q] = 0       (q != p),
H[R_p*chi_p^2] = H[R_p].
```

These are `rest_distinct_character_zero` (`:198`) and `rest_square_moment`
(`:220`). They are statements under R_p, NOT orthogonality under A. The
second uses the SU(2) character identity chi_1^2=1+chi_2. The stronger
spectator theorem retains an explicit missing-link locality hypothesis:
`rest_character_spectator_zero`, same file `:172`.

## Finite reciprocal tests in the full original action

The positive local window L(w)<=S_p<=U(w) has

```
L(w) = min(headFloor(w),1)^24,
U(w) = (1+prefixCap(w))^24.
```

The constants and certificates are `lower`, `upper`, `starLowerCertificate`
and `starUpperCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryWindow.lean:45`, `:46`,
`:127`, `:141`. The reused head floor/cutoff are `headFloor`, `headCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50`, `:55`;
the upper input is `prefixCap`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:117`.

Use the existing finite polynomial reciprocal G_p,k of S_p. Set
d_p,k=chi_p*G_p,k and retain the finite residual e_p,k. The exact identity
S_p*d_p,k+chi_p*e_p,k=chi_p is `cancellation_pin`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDual.lean:69`;
`dualTest` and `residualPolynomial` are defined in that file at `:50`, `:63`.

The finite norm proof uses the positivity certificate

```
1-L*S*G_k^2 = [1-(S*G_k)^2] + S*(S-L)*G_k^2.
```

This is `localDualNormCertificate`,
`lean/YMGap/Continuum/QuaternionHaarLocalDualNorm.lean:43`.
Its integral consequence is `local_dual_norm_le`, same file `:72`.
The actual-action specialization, `fullAction_norm_bound`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDual.lean:91`, proves

```
L(w)*H[A*d_p,k^2] <= D_p,       D_p = H[R_p],
```

for EVERY finite degree k. No inverse limit, bound on the inverse alone,
or independence of shared variables is used.

## Signed-family consumer and quantitative residual

`faceSpan` and `coefficientAt`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualPairing.lean:49`, `:53`,
retain the literal finite signed list. Repeated face labels contribute their
combined coefficient; the observable list need not be nodup. For its sum F,
`rest_signed_pairing`, same file `:116`, proves

```
H[R_p*chi_p*F] = coefficientAt(p,F)*D_p.
```

The full-action identity and error estimate are `fullAction_signed_pairing`
and `fullAction_signed_pairing_error`, same file `:143`, `:175`:

```
H[A*d_p,k*F] + err_p,k(F) = coefficientAt(p,F)*D_p,
err_p,k(F) = H[R_p*chi_p*e_p,k*F],
L(w)*err_p,k(F)^2 <= rho(w)^(2k)*D_p*H[A*F^2].
```

The error theorem uses weighted Cauchy--Schwarz, the actual residual interval
and floor insertion, not a coefficient l1 estimate:
`local_dual_pairing_error`,
`lean/YMGap/Continuum/QuaternionHaarLocalDualNorm.lean:123`.
Its single factor L is retained by the specialization.

`rate`, `rate_nonnegative`, `rate_lt_one`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDual.lean:133`, `:136`,
`:141`, supply rho(w)=1-L(w)/U(w) in [0,1).
`approximationCutoff` (`:159`) and `residualApproximationInterval` (`:163`)
return an explicit degree for any positive residual tolerance, valid at every
later degree.

The quantitative hypotheses include 0<w<1, K>=headCutoff(w), selected
physical action labels and `ids.Nodup`. L, U, rho and the residual tolerance
modulus are independent of extent, selected-factor count and plaquette label.
They depend explicitly on nome. D_p and the input norm still depend on the
selected action and regulators: this is NOT an absolute volume-uniform error
bound. No bare-coupling/spacing-uniform positive mass is claimed. The gauge
data are quaternion/SU(2), not arbitrary compact groups.

## Next causal frontier: no new gap claimed

1. The simultaneous dual-family Gram estimate is OPEN. Establish locality of
   the actual finite reciprocal tests, bound the overlap relation of selected
   physical faces, and control non-overlap cross terms with explicit residuals.
   No final constant may grow with volume or the number of distinct labels.
   The current single-dual norm and pairing do not supply this theorem.
2. After the family estimate, apply it to the original signed adjacent-time
   jump. Reuse `windowRatio_span_mul_originalFiniteValue`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowProbeSpan.lean:215`, and
   the factor-two identity `normalizedEnergy_window`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:109`.
   This specialization has NOT been proved for the new dual family here.
3. Separately, an original spatial variance/susceptibility UPPER bound in the
   combined coefficients is still needed with appropriate parameter control
   beyond the small-nome guard or along a justified scaling trajectory.
   Locality of V does not imply locality of the actual terminal messages;
   no message-erasure argument is supplied by this increment.
4. Only the combined energy lower and variance upper bounds can feed the
   EXISTING consumer `clearedDefect_diagonal_nonnegative_iff`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
   Products, physical transfer orbit and dense-sector coverage remain open
   beyond these fundamental signed sums. Physical scale calibration,
   same-theory continuum/QFT reconstruction and all compact simple groups
   remain open. No canonical target or analytic guard was weakened.

## Verification

All five new modules passed focused serialized one-worker / 20 GiB checks.
All 47 printed gates lie within {propext, Quot.sound}; `lower`, `upper` and
`coefficientAt` are axiom-free. Final logs have no errors or warnings.
Independent source review passed the certificate identity, the single L
factor, original-action normalization, signed duplicate handling and explicit
finite residual. It emphasized the regulator dependence of D_p retained above.

| Final log | SHA-256 |
|---|---|
| `/tmp/ym-local-dual-norm-20260917.log` | `5a9a70ce47bc56c31727705138fa51905ddb488c145a4c57b4acc4aa7c640f20` |
| `/tmp/ym-plaquette-boundary-erasure-20260917.log` | `7c7c5a16a493424ab844a594ac59b1281ae49ae77bc064d9ea46ece7b7e7f765` |
| `/tmp/ym-plaquette-boundary-window-20260917.log` | `70d590ab27ae4a36b594bf2ce84d9ade167935187bba3bf3a98e4467d0c1dce0` |
| `/tmp/ym-plaquette-boundary-dual-20260917.log` | `80b0bd9dd805a461ccf011936c06cde3441c792904c1c35ed12c87c75961678c` |
| `/tmp/ym-plaquette-boundary-dual-pairing-20260917.log` | `831873e0fce80981cb61f89be77dc0e28ea9e2a2c7cd51ec4042692049843a5a` |

No sorry, axiom, analytic assumption, canonical field or resource limit was
introduced or changed. Five semantic-root imports were added. Full-root
build, full axiom audit, guard and progress suite were NOT run; the hashed
full-audit baseline was not regenerated. CI remains unchanged.
