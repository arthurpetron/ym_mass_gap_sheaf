# Actual centered transfer quadratic to the original completed bond norm

Date: 2026-10-01 UTC. PROVED at fixed nome and spatial width for supplied
single-slice Wilson expressions. This closes the moving-center finite-to-bond
join identified after `86ddb59`, without equating the finite odd marginal
variance with the adjacent-time bond norm.

## Finite identity

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredTransferCovariance.lean`.
`normalizedCenteredTransferQuadratic` at :61 is

    B/Z = H[V*(g*psi)*T(g*psi)] / oddMass,
    g = terminalMessage(depth), psi = ACTUAL oddCentered(f).

`normalizedCenteredTransferQuadratic_window` at :73 composes the original
`edge_pairing` and `edge_window_pairing`, then divides by the SAME already
proved-positive oddMass. This is definitionally the denominator of the
one-step window (depth,1,depth); no new partition is introduced.
`normalizedCenteredTransferQuadratic_covariance` at :108 proves

    B/Z = W(f0*f1) - W(f0)*W(f1).

The actual finite normalizedMoment is rationally equivalent to the existing
middleRatio by `marginalMoment_pin`. Polynomial coefficient congruence
transports BOTH centered insertions. `centered_product_pin` then uses its
already-proved endpoint-mean equality; no limiting mean replaces a finite
one. The theorem covers every supported signed one-slice polynomial with
0<w<1 and headCutoff(w)<=K.

## Original Wilson sources and explicit independent regulators

All declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredTransferBondLimit.lean`.
`singleSlice` at :74 consumes e and Within(0,e), returning the intrinsic
source x with literal radius zero. Its three crossOdd sources are exactly
(shift(1,e))*e, (shift(1,e))*one, and one*e. They all fit in the SAME
one-step window with cutoff headCutoff(w)+k and exterior depth t.

`connectedScalar` at :167 keeps these three originalWindowScalar terms.
`finiteScalar` at :172 is the actual normalized centered transfer quadratic.
`finiteScalar_connected_pin` at :177 equates them using supported padded
source pins, retaining units, Wilson order, signed coefficients and both
original finite means. No false finite symmetric-depth padding is used.

The computed absolute mean ceiling is P=max(1,cap(upper),cap(lower)).
`jointTolerance` at :218 is epsilon/(1+2P); pair error d and product error
2P*d sum to epsilon. `cutoffThreshold` and `timeThreshold` at :238 and
:243 take the maxima of the THREE existing fixed-source thresholds at d.
`finiteScalar_rectangle` at :271 bounds every independent late pair (k,t)
and (j,s), not only a joint diagonal or an exchanged limit.

`transferCauchy` at :310 returns the diagonal QCauchy witness with modulus
max(cutoffThreshold,timeThreshold). `transferLimit` at :316 constructs its
CReal. `transferLimit_approx` at :320 exposes both raw regulator thresholds
and the representative cutoff for the full rectangle.

## Exact SAME completed-carrier pin and residue

Three existing originalJoint_diagonal_converges results and constructive
scalar arithmetic identify the limit as joint(pair)-joint(upper)*joint(lower).
`transferLimit_completed_pin` at :355 identifies its RC class with
connected(0,ofSource(x),ofSource(x)) on the EXISTING physical BondCompletion,
using original bondForm and connected_source_pin. No new norm, action,
vacuum, source algebra or analytic premise is supplied.

OPEN: arbitrary radius>0 multitime inputs are not one-slice observables;
passing the finite ANGULAR estimate needs a constructed limiting or
lower-semicontinuous angular form for the varying outputs. The useful complete
signed energy/SAME-variance estimate on a justified scaling family, spatial
and spacing control, nontrivial continuum survival, physical mass calibration,
canonical continuum OS/QFT and every compact simple group remain OPEN.
No canonical field or displayed chart marker changes; no ASCII is reprinted.

## Verification

Both final focused checks exited zero. Fifteen exported axiom gates passed:
singleSlice is axiom-free; the other fourteen depend exactly on
{propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide, noncomputable declaration or frontier weakening was introduced.
Initial missing namespace, explicit syntax/support simplification and whnf
elaboration errors were repaired; opaque original objects and a generic
scalar lemma resolved the timeout without raising any limit.

Main alone compiled through the safe-build skill with one worker, a 20 GiB
worker ceiling, 12 GiB OS reserve and dynamic telemetry. Preflight found no
competing compiler/runner, 83 percent pressure-free memory and zero swap.
No full root/tree build, broad audit or guard ran. Root import registration
is not aggregate-root checking; CI remains manual-only.
Independent read-only mathematical review found no source/partition/scope
mismatch. A separate source/log review confirmed all fifteen gates, explicit
Type-valued moduli, independent regulators and the radius-zero target.
The completed join returns witnesses and explicit moduli, not a new assumed
convergence field. A lower-semicontinuous angular construction would suffice
for the next reserve consumer; strong convergence of the raw unnormalized
terminal outputs is neither claimed nor imposed as a necessary prerequisite.

Accepted logs and SHA-256:

- `/tmp/ym-centered-transfer-covariance-accepted-20261001.log`:
  `c993132620284969f22f191fd9cdd5d31942bece9f38988beee4656199784a12`.
- `/tmp/ym-centered-transfer-bond-limit-third-20261001.log`:
  `fa120e1e1dcb968713695927a9ca0daabad5aa58986de466022e9cb7af3fdd42`.
