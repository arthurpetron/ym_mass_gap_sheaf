# Original one-plaquette Ward calculation

2026-10-02 UTC. This is an exact finite original-source calculation, not a
variance-relative estimate, a scaling result or a closed Clay obligation.

## Mathematical result

Fix 0<w<1, width, K>=headCutoff(w), terminal depth n and a literal original
spatial face. Write f=chi_1(plaquette), W=V*g_n*g_(n+1), and
m_l=H[W*chi_l(plaquette)]/H[W]. The original terminal messages, spatial
action and OWN marginal mean remain unchanged. The checked identities are

    OWNVar(f)       = 1 + m2 - m1*m1
    angularCost(f)  = 4*(3 - m2)
    completeWard(f) = 16*m2 - 12*(m1*m1).

These follow from the coefficientwise fusion identity chi_1^2=1+chi_2,
literal four-link curvature Gamma(f,f)=4*(4-f^2), and the complete original
Casimir Ward law angularCost+completeWard=12*OWNVar. Fusion is not a
bare-Haar substitution. The differentiated complete weight is expressed
exactly in two ORIGINAL interacting character moments, not discarded.

Strict padding base<width joins the angular identity to actual temporal
energy, with h=1-w and the existing complete signed normalized remainder R:

    E(f) = 4*h*(3-m2) + R
    varianceRemainder(f) = R - h*(16*m2 - 12*(m1*m1)).

Neither a sign nor a useful rate for R, m1 or m2 is assumed or proved.

## Declaration map

All new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean`:

| Declaration | Module:line | Role |
| --- | --- | --- |
| `plaquetteMoment` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:71` | Computes the original middleRatio(n+1,n) for each character label. |
| `plaquette_variance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:145` | SAME OWN-centered variance, including the actual squared mean. |
| `plaquette_angular` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:165` | Exact physical label-two deficit, with original complete marginal. |
| `plaquette_ward` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:200` | Expresses the complete signed weight derivative in m1,m2. |
| `padded_plaquette_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:250` | Actual temporal energy retains the SAME signed Taylor remainder. |
| `plaquette_variance_remainder` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean:266` | The existing variance correction with its exact SUBTRACTED Ward term. |

Source pins: `marginalMoment_pin` and `marginalVariance_pin` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:64` and
`:93`; literal curvature `plaquette_gamma` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCurvature.lean:129`;
fusion `first_character_square` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatPlaquetteSquare.lean:32`.

## Actual consumer and remaining frontier

The supplied reference estimate consumed by `completed_reference_ratio` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
can now be tested on one plaquette without estimating its weight derivatives.
At reference depth s+1 the actual quantities to compare are
4*h*(3-m2)+R and c*(1+m2-m1*m1), for ALL late cutoffs. This calculation does
not supply that comparison, its useful changing-family rate or the original
cross-scale maps. Signed multi-face families retain their cross terms; this
one-face calculation does not replace the whole-family estimate.

Angular/Ward formulas apply to an actual face in the given width. The temporal
formula requires STRICT padding. No width-one fringe-kernel result is used as
an estimate for a padded face. No Gaussian approximation or original-source
counterexample is asserted. Nonzero continuum survival, physical mass, full
same-theory QFT, every compact simple group and Clay remain OPEN.

## Verification boundary

Focused command, from the repository root:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteWardMoments.olean --log-file /tmp/ym-plaquette-ward-moments-small-20261002.log
```

Exit 0; six public gates, all {propext,Quot.sound}; no errors, warnings or
sorryAx. No new sorry, axiom, analytic input, witness erasure or weakened
frontier. Local opacity avoids unfolding original masses and variances during
scalar normalization; no heartbeat or memory limit was raised. One 20-GiB
worker, 12-GiB OS reserve, monitored telemetry; no competing compiler. Host
pressure was low, swap zero before the check, and no compiler survived it.

Luna independently reviewed the original weight, mean, normalization, signs,
padding scope, all six final source/log gates and both recorded hashes.
Parallel source review found no ready stronger original
variance floor or padded-width reference estimate; no redundant generic
counterexample or hypothetical compiler was added.

| Artifact | SHA-256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialPlaquetteWardMoments.lean` | `13ff8d2916ab34ba017d15e7e3b90e0b87388bdcb67b1a3bbd3f957b40f16be6` |
| `/tmp/ym-plaquette-ward-moments-small-20261002.log` | `88665fda266de84ec131c3131ffb0897b01b6a9ec2bdfd321723432eb35bcf6f` |

Earlier draft, second and opaque-named logs contain failed elaborations and
are NOT verification evidence. One semantic root import added; the full
root/tree build, axiom audit, guard and progress-metric script were NOT run.
CI remains off. No exact displayed canonical chart claim changed; no reprint.
