# Original completed chronological area coercivity

## Whole-project goal and scope

OPEN: constructive continuum Yang--Mills on R^4 for every compact simple
group, with SAME-theory QFT axioms, nontriviality and a finite positive physical
Hamiltonian mass gap. This checkpoint concerns finite-volume SU(2), ordinary
original-action weighted L2 and its conditional projections. It is NOT an OS
transfer identification or physical mass-gap theorem.

## Exact bound and parameter dependence

For 0<w<1, write L=headFloor(w), U=prefixCap(w), N for the actual physical-link
count, C=12*(extent+1)^3, and K>=headCutoff(w). The checked coefficient is

    B = N * (U/L)^(2*C+12) > 0,     alpha = 1/B > 0.

For every state x orthogonal to the original constant vector in the SAME
completed full-action form:

    alpha * normSq(x) <= finalEnergy(schedule extent, x),
    normSq(x) <= B * finalEnergy(schedule extent, x).

Here finalEnergy is the sum of squared residuals of the pre-existing
conditional projections, all evaluated on x. It is not a sum evaluated along
successive updated states. The chronological permutation changes the order
of this finite sum, not the conditional sweep operator.

The completed declarations parameterize K as headCutoff(w)+stage, for every
stage. Dense statements allow arbitrary K with the explicit lower-cutoff
guard. B and alpha have no K, stage or observable argument. Nome and extent
remain explicit; no beta/spacing-uniform assertion or continuum calibration
is supplied. The area-dependent exponent is retained, not absorbed into an
opaque constant.

## Checked causal joins

All file paths in the table are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `originalPartition` | `BF4ExactSlabOriginalVariancePins.lean:37` | Literal original full partition Z=H[W] |
| `originalPartition_positive` | `BF4ExactSlabOriginalVariancePins.lean:40` | Constructed positivity justifies cancellation |
| `original_norm_pin` | `BF4ExactSlabOriginalVariancePins.lean:53` | Existing unnormalized norm equals H[W*p^2] |
| `original_mean_pin` | `BF4ExactSlabOriginalVariancePins.lean:59` | Centering uses H[W*p], not free Haar |
| `centered_determinant_pin` | `BF4ExactSlabOriginalVariancePins.lean:66` | Original D(p)=Z*F.B(p,p) for centered p |
| `areaFaces` | `BF4ExactSlabChronologicalCostBound.lean:41` | Explicit C=12*(extent+1)^3 |
| `faceRatio` | `BF4ExactSlabChronologicalCostBound.lean:45` | Constructive rational U/L |
| `areaCost` | `BF4ExactSlabChronologicalCostBound.lean:82` | Reciprocal positive floor times matching cap |
| `chronological_stepCost_le_areaCost` | `BF4ExactSlabChronologicalCostBound.lean:205` | Every actual step cost bounded by the common budget |
| `areaCost_eqv_faceRatio_pow` | `BF4ExactSlabChronologicalCostPower.lean:60` | Exact ratio exponent 2*C+12 |
| `chronologicalResidualEnergy_sum` | `BF4ExactSlabChronologicalDirichletSum.lean:124` | Existing finalEnergy, same input and every actual link once |
| `poincareCost` | `BF4ExactSlabChronologicalCoercivity.lean:75` | B=N*areaCost, no partition factor |
| `blocks_positive` | `BF4ExactSlabChronologicalCoercivity.lean:80` | Explicit time-zero plaquette witnesses N>0 even at extent zero |
| `areaCoercivity` | `BF4ExactSlabChronologicalCoercivity.lean:102` | Witnessed positive reciprocal alpha |
| `dense_centered_poincare` | `BF4ExactSlabChronologicalCoercivity.lean:145` | Exact cancellation of common 2*Z in the chronological path bound |
| `dense_centered_area_coercivity` | `BF4ExactSlabChronologicalCoercivity.lean:175` | Dense lower Dirichlet coefficient |
| `completed_centered_area_coercivity` | `BF4ExactSlabCompletedChronologicalCoercivity.lean:42` | Same coefficient for every completed centered state |
| `completed_centered_area_poincare` | `BF4ExactSlabCompletedChronologicalCoercivity.lean:59` | Equivalent completed upper Poincare bound |

Completion reuses `centeredCauchy`, `centeredCauchy_modulus` and
`centeredCauchy_same_class` at
`lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:98`,
`:105` and `:192`, respectively. The coefficient-parametric closure is
`completed_of_termwise_bound` at
`lean/YMGap/Continuum/BF4ExactSlabCompletedFiniteVolumeCoercivity.lean:155`.
No representative choice, new completion, or assumed analytic bound is added.

## Verification boundary

Six final focused checks passed with one worker, 20 GiB compiler ceiling,
12 GiB OS reserve and automatic memory telemetry. All 28 printed gates are
within {propext, Quot.sound}. Checks finished within their initial calls;
there was no live long-running compiler to poll. No full-root build, audit
or guard was run, including no integrated root-import build.

Final logs:

- `/tmp/ym-original-variance-pins-20260930.log` (4 gates)
- `/tmp/ym-chronological-cost-bound-20260930.log` (11 gates)
- `/tmp/ym-chronological-cost-power-20260930.log` (2 gates)
- `/tmp/ym-chronological-dirichlet-sum-20260930.log` (3 gates)
- `/tmp/ym-chronological-coercivity-20260930.log` (6 gates)
- `/tmp/ym-completed-chronological-coercivity-20260930.log` (2 gates)

Sol developed the scalar cost/exponent and exact finite-sum joins in parallel;
compiler checks remained serialized. Luna's independent source review found
no normalization, factor-two, carrier, centering or completion issue; it
confirmed the late-cutoff-only uniformity and conditional-L2 scope.
No sorry was introduced or discharged,
no custom axiom or analytic premise was added, and no frontier type weakened.

## Remaining mathematical work

The finite normalization/area-budget branch is now complete. Its explicit
area loss does not establish the required spatial/scaling control. The next
priority is the missing cancellation-preserving collective signed producer on
a justified scaling family, using existing consumers rather than further
wrapping this finite bound. OS/physical-time identification, nontrivial
continuum survival, finite physical mass, full QFT and every compact simple
group remain open. No canonical chart node changed; no ASCII reprint.

### Source-reviewed next consumer (not a new proof)

`reverse_energy_of_coercivity_at_balanced` at
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:156` needs
Dirichlet coercivity only at the actual balanced output B*u and converts
delta into c=2+2*delta/625. The coefficient-parametric
`finiteCovariance_sq_bound` at
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102` consumes
the reverse inequality at `(coupled ... c x n).2`, retaining the original
centered x, both diagonal variances and grow(16*n) separation. The auxiliary
depends on c: a changed coefficient must be proved on its own auxiliary.
The specialized `BF4ExactSlabFiniteVolumeChebyshevRate.finiteCovariance_sq_rate_bound`
is still tied to its previous coefficient; it does not automatically use the
new area coefficient. A useful scaling-family estimate for these consumed
outputs is the narrower next target. This source review supplies no such
estimate and no physical-time calibration.
