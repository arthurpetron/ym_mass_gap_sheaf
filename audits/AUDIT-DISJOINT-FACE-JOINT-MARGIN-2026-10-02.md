# Joint control of original disjoint face covariance and temporal energy

The new argument joins the ORIGINAL interacting covariance and mixed temporal
energy in one Haar Gram pairing. It retains both interacting means, the exact
signed heat-weight difference and the entire cubic/cutoff debt. It does not
prove positive margin, a useful scaling rate or a continuum mass gap.

The complete module, computed matching scale and direct original reference
margin consumer passed a warning-free focused Lean check. All nineteen public
axiom reports contain only {propext,Quot.sound}. Independent mathematical and
source review passed. This is joint finite control, not a favorable margin.

## Mathematical argument

Let h=1-w, a be the ACTUAL projected endpoint source, Z the original odd
partition, and f,g the two signed singleton spatial spans. The original
marginal is W=V*g_n*g_(n+1); it is not a*a. For these padded observables only,
the existing projection theorem preserves its moments against a*P(a).

Both means mu_f,mu_g are computed under W. Set

```
u = a*(f-mu_f),             v = a*(g-mu_g)
B_f = a*C(f)-2*Gamma(a,f),  B_g = a*C(g)-2*Gamma(a,g)
r = B_f-lambda*u,           s = B_g-nu*v
D = H[a*(P(a)-a)*(f-mu_f)*(g-mu_g)]
J = Z*(2*c*Cov_W(f,g)-E_mix).
```

Here lambda and nu are rational residual scales, distinct from the means.
H is the ordinary finite Haar pairing, not a claimed physical OS norm.
Haar integration by parts proves H[a*B_f]=0 and
H[a*g*B_f]=H[a*a*Gamma(g,f)] for arbitrary source and tests. No Casimir
eigenmode or source-positivity premise is needed. Literal link-disjointness
then gives H[u*B_g]=H[v*B_f]=0, even at the ORIGINAL interacting centers.

The two surviving terms in the residual pairing give

```
H[r*s] = H[B_f*B_g] + lambda*nu*H[u*v]
H[u*v] + D = Z*Cov_W(f,g).
```

The second equality transports only the padded centered product through
inactive-source projection. It does not identify W with a*a or assume
independence of either original source. Combining it with the existing
second-order mixed-energy identity, when h^2*lambda*nu=2*c, gives

```
J = h^2*H[r*s] + 2*c*D - mixedDebt
(J + mixedDebt - 2*c*D)^2 <= h^4*H[r*r]*H[s*s].
```

Thus OWN covariance and commutator cross are estimated together, rather than
bounded separately by absolute values. The final inequality is sharp Haar
Cauchy--Schwarz on the two actual residual polynomials. Their norms and both
signed corrections remain unestimated on the required changing family.

## Source and original consumer

The new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean`.
`jointMargin` is the actual mixed contribution to c*OWN variance minus
temporal energy, cleared by the SAME odd partition. Its consumer retains
0<w<1, original head cutoff, literal disjointness, physical face membership
and strict padding. There is no extra sufficientCutoff guard.

The already-proved `centered_cross_pin` in
`lean/YMGap/Continuum/QuaternionHaarPredictionCovariance.lean` is now public
and separately axiom-gated. Its proof and statement are unchanged; this avoids
duplicating the generic two-mean covariance calculation.

The computed `matchingRightScale` sets lambda=1 and nu=(2*c)/h^2 using
`Q'.recipPos`. `matchingRightScale_pin` proves the matching equality for
EVERY rational c when w<1; no square root, choice or matching hypothesis
needs to be supplied. This does not bound the resulting residual squares.

`reference_margin_difference_pin` identifies the SAME-cutoff/depth quantity

```
Z*(referenceMargin([p,q])-referenceMargin([p])-referenceMargin([q])) = J.
```

All three reference margins use K=headCutoff(w)+stage, the same coefficient
function, original action, depth and OWN means. This identity needs no
disjointness; disjointness is required to apply the preceding joint bound.
No successful finite checker or positive certificate is assumed or produced.

The central declaration anchors are:

| Declaration | Source |
|---|---|
| `commutator_pair` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:96` |
| `commutator_source_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:145` |
| `centered_commutator_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:164` |
| `disjoint_gamma_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:208` |
| `originalCenter`, `ownCovariance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:234`, `:239` |
| `source_covariance_defect_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:352` |
| `joint_margin_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:476` |
| `corrected_joint_margin_square_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:495` |
| `matchingRightScale`, `matchingRightScale_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:534`, `:538` |
| `reference_margin_difference_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:668` |
| Existing `centered_cross_pin`, now public | `lean/YMGap/Continuum/QuaternionHaarPredictionCovariance.lean:97` |

## Verification

Accepted checks (both EXIT 0, no warnings or errors):

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/QuaternionHaarPredictionCovariance.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarPredictionCovariance.olean \
  --log-file /tmp/ym-own-centered-covariance-20261002.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.olean \
  --log-file /tmp/ym-disjoint-face-joint-accepted-20261002.log
```

The new module's nineteen public gates are `commutator_pair`,
`commutator_source_zero`, `centered_commutator_zero`, `disjoint_gamma_zero`,
`originalCenter`, `ownCovariance`, `centeredSource`, `residual`,
`residualSquare`, `heatCovarianceDefect`, `jointMargin`,
`own_covariance_mass_pin`, `source_covariance_defect_pin`, `joint_margin_pin`,
`corrected_joint_margin_square_bound`, `matchingRightScale`,
`matchingRightScale_pin`, `familyReferenceMargin` and
`reference_margin_difference_pin`. The covariance module's four gates are
`normalizedCovariance`, `centered_cross_pin`, `normalizedVariance_nonnegative`
and `covariance_sq_le_variance_deficit`. EVERY printed dependency set is
{propext,Quot.sound}; no `sorryAx`, choice, native evaluation or new axiom.

SHA256, recorded from the accepted sources and logs:

| Artifact | SHA256 |
|---|---|
| New joint-margin source | `b6576b5a5ee21085d0f4a374042400c063343463b173b0cd0814165a28e1dde6` |
| `/tmp/ym-disjoint-face-joint-accepted-20261002.log` | `006c00473275e9c94af1749552b5b1e12eb840051feee40fc1294e58fb355db7` |
| Covariance source | `e9fa843c47bf4fd6d32a05188c1fced79dbcc1ef6f7d24308a962be70f4b50d6` |
| `/tmp/ym-own-centered-covariance-20261002.log` | `f00a5d77504eae725d343df0c2635398da473b25e0cc9264c2a7cffd03926c89` |

Earlier draft failures were namespace/import, congruence argument-order,
scalar elaboration and list-membership issues; those logs are NOT acceptance
evidence. Abstract scalar algebra removed the elaboration bottleneck without
raising limits. Two unused-variable warnings in the final draft were fixed
before the accepted rerun. Sol independently passed the final signs, computed
matching scale, original moment-only projection and direct finite consumer.
Luna independently matched every source/log hash, all twenty-three gate
outputs and declaration lines, and the byte-identical status-chart fence.

The root alone uses ONE capped 20-GiB worker with the unchanged 12-GiB reserve.
Preflight found no competing compiler/runner/test; free-memory pressure was
86 percent and swap was zero. Postcheck free-memory pressure remained 86
percent; the separate postcheck sysctl query was permission-denied, so no
postcheck swap assertion is made. One root import is registered, but the root
aggregate and full tree were NOT checked. No broad build, audit, guard, metric
or heavy evaluation was run. The parallel paper review reuses cached primary
sources; it supplies no new analytic premise or quantitative estimate here.

## Remaining input

A useful original signed margin still needs joint control of the residual
squares, signed heat defect, mixed debt and diagonal margins, exceeding the
existing common cutoff allowance on a JUSTIFIED changing family. No favorable
original instance or scaling coefficient is supplied. Spatial/spacing control,
every-state scaling decay, nonzero continuum survival, physical mass, full QFT,
every compact simple group and Clay remain OPEN. No displayed status-chart
claim has changed; no ASCII reprint is justified.
