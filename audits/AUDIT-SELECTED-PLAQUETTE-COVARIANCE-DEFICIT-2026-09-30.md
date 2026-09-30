# Original selected-action plaquette covariance deficit

Date: 2026-09-30 UTC. Whole-project Clay target remains OPEN.
Classification: PROGRESS on a supplied original-source estimate, not closure
of the primary scaling-family frontier. Canonical chart unchanged.

## Why this direction

`BF4ExactSlabStarFullActionProbe.fullData`
(`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`) uses the full
physical face list. `BF4ExactSlabConditionalSweep.projections`
(`lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:56`) acts on that
data. Changing its update schedule does not change its underlying measure
to the selected-chart action. We did not identify those actions or their
completed carriers.

Instead, the existing selected-action prediction floor supplies a direct
scalar estimate. No generalization of the full-slab completion is needed.

## Short mathematical argument

Let p be the actual fundamental plaquette character and q a supported
polynomial missing one actual edge of that plaquette. Keep the original
selected heat product W and its own positive partition Z throughout.
For every rational affine predictor a+t*q, the existing theorem supplies

    E_W[(p-a-t*q)^2] >= s(w),  s(w)=starRatio(w)>0.

Choose a=E_W[p-t*q]. With A=Var_W(p), B=Cov_W(p,q), C=Var_W(q), this gives

    s <= A-2*t*B+t^2*C  for every rational t.
    B^2 <= (A-s)*C.

For C>0 the explicit test is t=B/C. For C=0, ordinary covariance
Cauchy--Schwarz handles the degenerate case; there is no division by zero,
classical choice, or assumed positivity of A-s. The actual character bound
gives A<=4, hence

    Cov_W(p,q)^2 <= eta(w)*Var_W(p)*Var_W(q),
    eta(w)=1-starRatio(w)/4,  3/4 <= eta(w) < 1.

## Checked declaration path

- `RationalPredictionCovariance.covariance_budget`,
  `lean/YMGap/Continuum/RationalPredictionCovariance.lean:66`: the scalar
  optimization, including zero test variance.
- `QuaternionHaarPredictionCovariance.covariance_sq_le_variance_deficit`,
  `lean/YMGap/Continuum/QuaternionHaarPredictionCovariance.lean:263`: exact
  centering and affine variance expansion on the SAME certified weighted
  quaternion-Haar law.
- `BF4ExactSlabSelectedPredictionCovariance.affine_prediction_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabSelectedPredictionCovariance.lean:75`:
  supplies every affine predictor from the already proved
  `BF4ExactSlabSelectedStarPredictionError.polynomial_square_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabSelectedStarPredictionError.lean:164`.
  Constants and scalar multiples preserve the required link locality.
- `normalizedCovariance_finiteCovariance`,
  `lean/YMGap/Continuum/BF4ExactSlabSelectedPredictionCovariance.lean:123`:
  exact pin to the existing finite covariance, including its own selected
  partition. `finite_covariance_deficit` at line 139 and
  `covariance_deficit` at line 162 prove the finite and cutoff-removed
  additive deficit for those same observables and action.
- `BF4ExactSlabSelectedPredictionRate.eta` at
  `lean/YMGap/Continuum/BF4ExactSlabSelectedPredictionRate.lean:56`,
  `eta_lower_bound` at line 58, and `eta_lt_one` at line 66 define and bound
  the explicit coefficient. `finite_covariance_rate` at line 127 and
  `covariance_rate` at line 161 prove the finite and cutoff-removed strict
  covariance factor, using the actual plaquette interval and positive law.

Both limit statements use the existing convergent original mixed covariance
and both diagonal covariances. They remove the heat cutoff at fixed extent;
they do not construct a spatial limit or identify completed carriers.

## Quantifiers and boundary

The actual-action theorems assume rational 0<w<1, an arbitrary duplicate-free
list of physical selected faces, an ambient physical plaquette, one of its
actual edges, and a supported test polynomial whose given link support omits
that edge. The source plaquette need not belong to the selected action list.
There is no small-nome guard or uninhabited analytic bound bundle.

The coefficient has NO extent, selected-list size, or late heat-cutoff
argument. It DOES depend on w. `starRatio` is defined at
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:46` from the
original heat floor and cap, with at most six incident physical faces.
The existing `starRatio_le_defect_power` at
`lean/YMGap/Continuum/BF4ExactSlabStarVarianceLossObstruction.lean:38`
records its deterioration toward w=1. No coupling- or spacing-uniform
strict separation from one is proved here.

This is ONE source-specific covariance factor. It has no distance or
iteration exponent. It is not a conditional-sweep spectral gap, a physical
OS transfer gap, every-state decay, or a continuum mass bound.

The precise iteration obstruction is that
`BF4ExactSlabSelectedStarPredictionError.retained_cross_zero`
(`lean/YMGap/Continuum/BF4ExactSlabSelectedStarPredictionError.lean:85`)
and `retained_error_identity` at line 145 use the fundamental plaquette's
erased-link moment identities. A conditional-transformed source is not
supplied with those identities. An invariant quantitative source class is
NOT FOUND in the bounded review of the above modules and
`BF4ExactSlabPlaquetteBoundaryDualFamily.family_partition_coercivity`
(`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualFamily.lean:376`)
and `BF4ExactSlabPlaquetteBoundaryDualGram.fullAction_gram_square_bound`
(`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualGram.lean:211`).
The latter two concern finite signed plaquette spans and their dual Gram
bounds, not an orbit-wide affine prediction floor.

NEXT: test the actual transformed source or a matched-physical-time signed
multiscale defect before proposing an iteration. No further generic budget
wrapper substitutes for the missing original scaling-family estimate.
Nontrivial continuum survival, same-theory OS/QFT construction, positive
finite physical mass and every compact simple group remain open.

## Verification

Final focused checks of all four new modules passed all 13 public axiom
gates; every gate reports only `propext` and `Quot.sound`.

| Module | Gates | Final successful log |
|---|---:|---|
| RationalPredictionCovariance | 1 | `/tmp/ym-prediction-covariance-rational-20260930.log` |
| QuaternionHaarPredictionCovariance | 3 | `/tmp/ym-haar-prediction-covariance-20260930.log` |
| BF4ExactSlabSelectedPredictionCovariance | 5 | `/tmp/ym-selected-prediction-covariance-20260930.log` |
| BF4ExactSlabSelectedPredictionRate | 4 | `/tmp/ym-selected-prediction-rate-20260930.log` |

All compiler invocations used the monitored safe launcher, one worker,
20 GiB hard worker ceiling, 12 GiB OS reserve and dynamic safety telemetry.
No concurrent compiler, broad build, full-root check, audit, or guard run.
Earlier elaboration errors were fixed; failed runs are not verification.
Explicit convergence types removed a reduction timeout without retaining
an increased heartbeat setting. Root imports were added but the full root
was not rechecked. Sol supplied scalar/weighted-Haar work and independent
scope review; Luna reviewed the selected-action boundary and drafted the
rate corollary, completed and checked by the root agent.

No new sorry, axiom, opaque analytic estimate or frontier weakening. No old
sorry discharged. The canonical chart's displayed claims did not change,
so it was not reprinted.
