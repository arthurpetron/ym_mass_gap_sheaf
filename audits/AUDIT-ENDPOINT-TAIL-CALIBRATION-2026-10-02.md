# Endpoint tail certificate cannot preserve a near identity heat floor

## Outcome and scope

For `1/2 <= w < 1`, every degree `L >= 1` satisfying the existing displayed
source-tail certificate

```
6*endpointRelativeCap(w)^2 <= (L+1)*(L+3)
```

has `3*w^(L*(L+2)) <= 1`. Thus that sufficient certificate cannot be combined
with even a one-half retained bare heat floor. The actual computed tail
modulus supplies the premise for `0 < epsilon <= 1`; the obstruction is not
based on an uninhabited input.

This bounds a number used in a PARTICULAR certificate, not the true source
tail below, original transfer response above, or true energy/OWN-variance
ratio. A sharper actual-source bound or signed cancellation is not refuted.
The whole-project continuum Yang--Mills and mass-gap target remains OPEN.

## Original inputs and mathematical argument

`BF4ExactSlabFixedSpatialEndpointRelativeBound.endpointRelativeCap`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:59`)
is `6*relativeCap(w,4096)+relativeCap(w,32)`. Its exact formula is
`24608*budget(w)+7`, not the different marginal score cap.

`BF4ExactSlabFixedSpatialEndpointSpectralTail.projectedEndpoint_highTail_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointSpectralTail.lean:111`)
uses the first omitted Casimir `(L+1)*(L+3)` to bound the raw one-link high
part of the COMPLETE original projected source. Width, terminal depth and
sufficiently late cutoff are quantified. This raw norm is not OWN variance.

`BF4ExactSlabFixedSpatialScoreCalibrationObstruction.squared_gap_budget_ge_one`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialScoreCalibrationObstruction.lean:38`)
gives `(1-w)^2*budget(w) >= 1` for `1/2 <= w < 1`. The exact endpoint cap
dominates `budget(w)`; with `0 < 1-w <= 1`, this implies
`(1-w)*endpointRelativeCap(w)^2 >= 1`.

Keep the two Casimirs distinct. For `L >= 1`,
`(L+1)*(L+3) <= 3*L*(L+2)`. Multiplying the displayed tail condition by
`1-w` therefore gives `2 <= (1-w)*L*(L+2)`.
`ReciprocalBernoulliUpper.oneSub_pow_mul_bernDen_le`
(`lean/YMGap/Continuum/ReciprocalBernoulliUpper.lean:103`) then gives
`3*w^(L*(L+2)) <= 1`. No logarithm, spectral existence theorem or asymptotic
limit is used.

The computed `endpointTailDegree`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointSpectralTail.lean:139`)
and `endpointTailDegree_sufficient` (same module, line 142) give
`6*C^2 <= epsilon*(L+1)*(L+3)` at every degree beyond that modulus. With
`epsilon <= 1` and `L >= max 1 endpointTailDegree`, the displayed certificate
follows. This holds for every eligible degree, not only the particular
exponent in the older endpoint-channel floor calculation.

## New checked declarations

All declarations below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointTailCalibrationObstruction.lean`.

| Declaration | Line | Exact claim |
| --- | --- | --- |
| `endpointRelativeCap_formula` | 42 | Computed endpoint cap equals `24608*budget+7`. |
| `gap_endpoint_square_ge_one` | 67 | `(1-w)*C^2 >= 1` on `1/2 <= w < 1`. |
| `tail_certificate_heat_weight_ceiling` | 112 | Every positive degree meeting the displayed certificate has retained heat weight at most one third. |
| `endpointTailDegree_heat_weight_ceiling` | 164 | The actual epsilon-to-degree modulus supplies that premise for `0 < epsilon <= 1`. |
| `endpointTailDegree_not_half_floor` | 183 | These certified degrees cannot supply a one-half bare heat floor. |

The theorem concerns the largest retained Casimir `L*(L+2)`; it does not
identify raw Haar norm with the physical OS norm. When applying a retained
degree floor to a finite heat cutoff, the usual `L <= K` condition still
has to hold; this scalar obstruction removes no cutoff guard.

## Verification and independent review

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointTailCalibrationObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointTailCalibrationObstruction.olean --log-file /tmp/ym-endpoint-tail-calibration-20261002-final.log
```

Exit 0, warning-free. All five public printed gates report only
`{propext, Quot.sound}`. The first draft failed because two imported power
names were ambiguous; it is NOT verification evidence. A selective namespace
open fixed the problem without raising any resource or heartbeat limit.
No `sorry`, new axiom, classical/native oracle, analytic premise or weakened
canonical field was introduced.

The check used one 20-GiB worker and the unchanged 12-GiB OS reserve. Pre/post
inspection reported 86% memory-pressure free and zero swap; no compiler or
runner competed before or survived after the check. Sol independently reviewed
the mathematics, Casimir accounting and scope: PASS. Luna independently
reviewed the constant definitions, actual modulus, public gates and absence
of forbidden source constructs: PASS.

| Artifact | SHA-256 |
| --- | --- |
| New Lean module | `decd0a1d31b4b9205943402df4df1b38c250bac52619e4c4ba059c023ba914c0` |
| Accepted focused log | `390c9bf2edf01575e60ea2c882b80e7f1f81335526c7549c7a6dccda1b305e8c` |

One semantic root import was added. A root/full-tree build, full axiom audit,
guard and progress-metric run were NOT performed. CI remains off. The exact
canonical ASCII block is unchanged and was not reprinted.

## Repointed frontier

Do not extend the existing absolute angular-tail budget into a near-identity
centered-source argument: the displayed sufficient tail estimate already
loses that floor. Its genuine fixed-nome regularity and tail results remain
valid. Obtain sharper actual-source control or retain cancellation in the
normalized original covariance/energy comparison before taking absolute values.

The signed consumer remains
`DisjointFaceJointDeterminant.reference_pairing_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:310`).
The same-source complement identity is
`CenteredTransferReserve.centered_transfer_quadratic_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredTransferReserve.lean:65`).
Neither gets a useful positive margin from the bound proved here.

OPEN: original signed pairing and diagonal estimates beyond the common cutoff
allowance on a justified changing family; centered-source/OWN-variance control;
spatial and spacing comparison; nonzero continuum survival; finite positive
physical Hamiltonian mass; full same-theory QFT; every compact simple group;
and the Clay theorem. No broad displayed proof node closed.
