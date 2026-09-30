# Original Wilson boundary kernel: a proved route correction

Date: 2026-09-30 UTC. Parent baseline: `917d527`.

The whole-project target is unchanged: constructive continuum Yang--Mills
on R^4 for every compact simple group, with the same theory's full QFT
structure, nontriviality and positive physical mass gap. This result rules
out a proposed finite-carrier step, not that target.

## Proved on the SAME all-nome Wilson completion

For every rational 0<w<1, the width-one centered origin plaquette v satisfies

    B(v,v) >= starRatio(w) > 0,       T(1)v = 0.

The actual width-one time operator is therefore not injective. This is not
merely a kernel in an auxiliary ordinary-Haar representation. More generally,
every spatial face with an inactive kinetic link has zero centered correlation
at every positive integer lag, and its centered vector is killed by T(1).
The interacting fully active bulk is not covered by the inactivity hypothesis.

## Exact causal proof

1. `window_connected_zero` in
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceCorrelations.lean:166`
   cancels the finite joint-minus-product expression with the SAME original
   partition, spatial action and both terminal messages.
2. `finite_connected_zero` in
   `lean/YMGap/Continuum/BF4WilsonAllNomeFringeCorrelation.lean:63`
   identifies those ratios with literal Wilson sources. Stage j>=1 ensures
   K=headCutoff(w)+j retains the fundamental character; no small-nome guard.
3. `connected_lag_zero` (`:131`) takes the shifted joint diagonal j+1 using
   the existing convergence moduli. Original padding/stationarity identifies
   both endpoint means with the same zero-window mean.
4. `centeredTimeMoment_zero` (`:143`) identifies that scalar with the SAME
   centered Wilson form. Source and lag stay fixed during the regulator limits.
5. `inactive_face_time_one_zero` in
   `lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:59` uses
   B(v,T(2)v)=B(T(1)v,T(1)v) and completed positive definiteness to prove
   equality of completed vectors.
6. `originFace_not_fully_active` (`:76`) identifies the width-one inactive
   far edge; `originPlaquette_time_one_zero` (`:84`) specializes the result.
   `completedTime_one_not_injective_width_one` (`:94`) uses the existing
   positive-norm witness to refute injectivity.

That witness is `plaquetteExcitation_ne_zero` in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteExcitation.lean:93`, derived
from `plaquetteExcitation_norm_floor` and `starRatio_positive`. No arbitrary
nonzero vector or analytic premise is supplied.

## Cross-width consequence, with means kept distinct

`padded_origin_time_one_ne_zero` in
`lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:112` proves that
the origin plaquette at every width padding+2 has NONZERO one-step image,
using the positive response floor and proved active-link padding.

`no_centered_plaquette_time_transport` (`:130`) rules out any function from
width one to that padded completion which preserves zero, maps the first
centered origin plaquette to the second, and intertwines one time step at
that vector. No isometry or linearity is assumed. Each vector is centered
by its OWN mean; a raw-loop inclusion is not assumed to preserve centering.

No checked cross-width theorem is contradicted. The header of
`lean/YMGap/Continuum/BF4WilsonAllNomeDenseTimeNaturalTransformation.lean:1`
expressly excludes completed-carrier maps and interacting-action comparison;
`denseObservableDiagram` (`:43`) is an intrinsic-syntax diagram. The new
obstruction makes that distinction mathematically consequential.

## Execution-plan correction

Do not pursue unrestricted injectivity of the full finite-width all-nome
time map: it is false at width one. Do not silently quotient away this
positive-norm OS state. The original carrier, action and correlators remain
unchanged. Physical-time work must instead address controlled interior/bulk
and spatial/scaling comparison with explicit fringe handling. Any proposed
completed width map must prove its actual pairing, centering and time
compatibility. The useful signed/SAME-interacting-variance estimate is open.

The kernel does NOT refute the strict UPPER contraction bound: a zero time
eigenvalue is compatible with it. It does not exclude approximate width
comparisons, bulk limits or continuum Yang--Mills. No full continuous-time
no-go theorem or canonical continuum field is changed here. A03, J02, J03
and all Clay endpoints remain open; the displayed chart is unchanged.

## Verification and collaboration

Both new modules passed focused checks through `scripts/safe_lean_build.py`
with `--jobs 1 --check-worker-limit-gib 20`, their individual source and olean
output paths. All nine final printed gates use only `{propext, Quot.sound}`.
The scalar-limit file passed first try. A zero-vector/time-zero name confusion
was repaired during review; a local-notation collision in the kernel proof
was repaired after its first check. Final scalar and kernel checks took
approximately 7.2 and 6.0 seconds. All checks completed in their initial
calls; no manual live-job polling or competing compiler. Automatic resource
telemetry remained active.

Root proved the limit pin and padded transport obstruction; Luna implemented
the kernel consequence; Sol independently reviewed geometry, carrier identity,
cross-width scope and plan correction. No sorry was introduced/discharged,
no new axiom or analytic input was added, and no frontier field was weakened.
Root imports were added; full-root/full-tree build, full audit and guard were
not run. No literature listing rescan was performed.
