# Sharper fourth moments under the original Wilson edge law

Date: 2026-10-01 UTC. PROVED supporting estimate after `a9c7189`.
This is a diagnostic heat-parameter estimate, not a physical scaling family,
SAME-interacting-variance comparison, or continuum Yang--Mills result.

## Actual mathematical advance

Write `h=2^(-6r)`, `w=1-h`, and `S=r*2^(3r)`, with `r>=22`.
The COMPLETE existing scalar `quarticBudget(w,S)` now obeys

    quarticBudget(w,S) <= 888*r^4*h^2.

The earlier diagnostic bound was `2968*2^(-4m)` at `h=2^(-3m)`, hence
order `h^(4/3)`. On the subsequence `m=2r`, the new estimate has nearly
quadratic order, with its explicit polynomial factor in r. No Lean logarithm
identity or justified physical coupling/spacing calibration is claimed.

Under the unchanged ORIGINAL complete two-slice edge density and terminal
source, for any supplied active ordered word U,

    H_edge[ ||U(x)-U(y)||^4 ] <= F(length)*888*r^4*h^2*Z,
    H_edge[ (chi_1(U(x))-chi_1(U(y)))^4 ]
        <= 16*F(length)*888*r^4*h^2*Z.

Here `F(length)=wordFourthFactor(length)` is the existing explicit fourth-power
word-length cost, and Z is the SAME `oddMass`. The second inequality also
holds after dividing BOTH sides by that original positive partition.
The trace jump is literal; it is not a surrogate distance observable.

## Scalar proof and exact guards

All declarations below are in
`lean/YMGap/Continuum/SU2HeatQuarticLogDyadicBudget.lean`.

- `logSplit` (:35), `logRate` (:41) and `logOnset` (:45) return actual
  computable data. The nome/defect are the existing `nome(2r)`/`defect(2r)`.
- `logHalf_guard` (:151) proves `1<=2*w^(4*(S+2))`.
  Its natural inequality uses `16r<=2^(3r)` and `S+2<=2S`.
- `logTail_guard` (:222) proves `w^(S^2)<=2^(-r^2)`.
  The existing reciprocal-Bernoulli estimate gives
  `w^(2^(6r))<=1/2`; `S^2=r^2*2^(6r)` pays the full squared-spin tail.
  `logTail_le_eighth` also proves the original producer's eighth guard.
- `logBudget_bound` (:382) reuses the existing complete head/tail formula.
  `(S+2)h<=2r*2^(-3r)` bounds its fourth-order head by `512*r^4*h^2`.
  Its `296*h^2` part is at most `296*r^4*h^2`. For `r>=22`,
  `r^2>=21r`, so `S^3*w^(S^2)<=r^3*2^(-12r)<=r^4*h^2`.
  The tail costs 80 times that quantity; `512+296+80=888`.

No source estimate, variance floor or analytic premise is assumed to make
this scalar optimization pass. The original `quarticBudget` is not changed.

## Original-object consumers

1. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:242`,
   `fundamental_jump_scalar_pin`, exposes the existing padded equality between
   the SAME fundamental trace jump and twice the scalar component of the
   SAME ordered lower/upper word difference.
2. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonQuarticIncrement.lean:113`,
   `jumpFourthMoment`, defines the ACTUAL fourth jump under
   `edgeDensity(w,K,width,terminalMessage(w,K,width,depth))`.
   `jump_fourth_le_word_square` (:121) inserts the padded equality four times
   on the original doubled carrier. The scalar fourth is bounded by squared
   quaternion norm under the SAME weight; `(2x)^4=16*x^4` gives the factor 16.
   No active-link hypothesis is needed by this purely kinematic step.
3. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLogQuartic.lean:42`,
   `logCutoff`, returns `max(headCutoff(w),S+3)+stage`, satisfying BOTH guards
   at every stage. `wordLogRate` (:53) retains literal word-length dependence.
4. `word_quartic_log_bound` (:67) applies the EXISTING actual-source
   `word_quartic_bound` to the new computed split and guards. All original
   spatial weights, spectator heat and terminal factors remain. Activity of
   every physical word link is explicit; uncoupled fringe links are not included.
5. `jump_fourth_log_bound` (:92) transports that result to the literal trace
   jump. `jump_fourth_log_normalized` (:108) divides only by SAME proved-positive
   `oddMass`, without a deteriorating source floor/cap comparison.
6. `wilson_energy_log_quartic` (:131) consumes the improved remainder in the
   ORIGINAL radial energy formula:

       2*Energy <= 2*mixedRadialMoment + 2*wordLogRate*oddMass.

   The mixed radial moment stays under the complete original edge law. It is
   not factored into expectations, silently bounded, or dropped.

## Parameter boundary and next causal input

The scalar rate depends explicitly on r (hence nome); the actual word rate
also depends on its ordered length. Width, terminal depth and later cutoff
stage do NOT enter the coefficient. The cutoff onset depends on nome and
the spin split. No completed width map, changing-observable convergence,
beta/spacing relation or physical-time sampling theorem is added.

The PRIMARY useful COMPLETE signed energy/SAME-interacting-variance scaling
estimate remains OPEN. Existing first alignment gives no smaller estimate
for the mixed radial moment; terminal positivity/support alone does not
supply it. The new quartic ceiling improves only the explicit quartic
remainder. It is not a new signed-family covariance floor or relative ratio.

OPEN: justified spatial/coupling/spacing control, nontrivial continuum survival,
positive finite physical mass, full SAME-theory continuum OS/QFT and field/UV
identification, and every compact simple group. No canonical field or chart
marker changes. The unchanged ASCII chart was not reprinted.

## Verification and independent review

Four final focused checks exited zero and emitted their target oleans.
Their 11+6+12+8=37 printed gates contain ten empty axiom sets, two `{propext}`
sets, and twenty-five exactly `{propext, Quot.sound}` sets. No new sorry,
axiom, Classical, native_decide, noncomputable declaration, analytic field,
weakened frontier or surrogate substitution was introduced.

Initial missing namespace, Nat-power/eqv orientation, scalar association and
unconstrained width-placeholder errors were repaired. Failed draft logs are
not proof evidence. Sol independently checked the final mathematical constants,
guards, original-object consumers and retained mixed-moment residue. Luna
independently checked final sources, all accepted gate counts/dependencies and
all four hashes. Reviewers ran no compiler; main alone verified serially.

Checks used `scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`,
with explicit `--check` and `--check-output` target paths. Dynamic telemetry
and the unchanged 12 GiB OS reserve remained enabled. Preflight found 85 percent
pressure-free memory and zero swap. No worker/memory/heartbeat limit was raised.
No full root/tree build, broad audit, guard or CI change ran. Root imports are
registered, not checked in aggregate; CI remains manual-only.

Accepted logs and SHA-256:

- `/tmp/ym-wilson-fourth-jump-pin-20261001.log`:
  `19e93eef3784973f8eeac1b9cfbe53aae4aacde0209f2d4cc06bcda487d2b694`.
- `/tmp/ym-wilson-trace-fourth-original-second-20261001.log`:
  `8eff5b20b19981fbcfbbaaa694d9d3434c6006bb77d2a93fe3bd2cf45be11036`.
- `/tmp/ym-log-quartic-scalar-checked-20261001.log`:
  `2e1ba5db045b6e94b12a53c5501ca8f63f81f80e9810e69e7687c2a84f7a9cb7`.
- `/tmp/ym-log-quartic-original-consumer-accepted-20261001.log`:
  `a9171254de56f7da912e774fc016fff31aa11fd24ce10e554fbfb2b2a24e13dc`.
