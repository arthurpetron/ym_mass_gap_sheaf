# Original positive-time response with a width-independent floor

## Goal and exact scope

The whole-project goal remains constructive continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap. This result is for SU(2),
at fixed rational nome 0<w<1. It is a positive-response LOWER bound, not an
upper decay estimate, a spatial-limit construction or a continuum result.
No canonical chart state changes.

The preceding local-band audit's proposed response join is now proved.
For an actual spatial face, with all four links active, the original
one-step centered response has the explicit floor

    c(w) = ell(w)^2 / [U(w)^2 * (w^(-12)+5)] > 0,
    ell(w) = headFloor(w)^28,
    U(w)   = prefixCap(w)^28.

The harmless 5 reuses the existing cost cap; no sharp-constant claim is
made. The constant does not depend on width, terminal depth or cutoff.
The finite theorem requires K>=headCutoff(w), K>=1, terminal depth n+1,
and a center m in [-2,2]. The actual finite marginal mean meets the last
condition by the existing character interval theorem. Strict padding
supplies all four active links for a fixed base face at every larger width.
There is no assertion of uniformity as w approaches 1 or along a physical
spacing family.

## Causal mathematical join

Use the previously constructed, certificate-positive spectator
A=V_complement*P_rest(V*u_n), independent of the four selected face links.
Every exterior factor and the entire earlier interacting input remain.
Write f for the fundamental face character, h=f-m and b=(w^(-12)f-m)*A.
The new exact identity is P(b)=h*P(A) under all supported Haar tests, for
the FULL original active-link kinetic map P.

For one selected edge i, R=P_erase(i)(A) is a literally i-independent
polynomial with P(A)=R under supported Haar tests. This erasure only
chooses a proof representative. It does not replace the original action,
partition or operator. Both A and R are certificate-positive. Set

    Q = H[A*R] = <A,P(A)>.
    D = <V*u_(n+1)*h,P(b)>.
    N = <V*u_(n+1)*h,P(V*u_(n+1)*h)>.
    Z = oddMass(n+1), the ORIGINAL window denominator.

One-edge Haar integration gives H[(A*R)h^2]=(1+m^2)Q and
<b,P(b)>=(w^(-12)+m^2)Q. The local lower band implies D>=ell*Q;
positive-kernel order and the upper band give Z<=U^2*Q. Exact kinetic
Cauchy--Schwarz yields D^2<=N*(w^(-12)+5)*Q. The positive original
partition and its cap prove Q>0; only then is Q cancelled. This gives
ell^2*Z<=N*(w^(-12)+5)*U^2 and hence N/Z>=c(w).

The finite centered expression is expanded into three FIXED original
Wilson observables before taking limits. The existing cutoff/time
convergence and stationarity identify the limit with the connected lag-one
moment. Existing mean/time pins then give c(w)<=B(v,T(1)v) on the SAME
completed plaquette vector and time operator at each fixed spatial width.
No varying-center convergence or cross-width isometry is assumed.

## Declaration evidence

Paths in this table begin at `lean/YMGap/Continuum/`.

| Declaration | Source | Role |
|---|---|---|
| `selected_pairing_spectator_full` | `SU2QuaternionProductHeatPlaquette.lean:313` | Full kinetic plaquette/spectator transmission |
| `plaquette_spectator_kinetic` | `BF4ExactSlabFixedSpatialPlaquetteSpectatorKinetic.lean:52` | Literal original face and active-link permutation |
| `shifted_square_moment`, `dual_source_moment` | `BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments.lean:163`, `BF4ExactSlabFixedSpatialPlaquetteSpectatorMoments.lean:181` | Exact one-edge spectator Haar moments |
| `active_erased_spectator`, `plaquette_spectator_dual_preimage` | `BF4ExactSlabFixedSpatialSpectatorDual.lean:58`, `BF4ExactSlabFixedSpatialSpectatorDual.lean:87` | Tested erasure and actual modulated inverse-heat identity |
| `kineticPair_quadratic_cap` | `SU2QuaternionProductHeatPositiveOrder.lean:68` | Positive order controls SAME reference quadratic |
| `oddMass_endpoint_kinetic_pin`, `oddMass_spectator_cap` | `BF4ExactSlabFixedSpatialSpectatorPartition.lean:60`, `BF4ExactSlabFixedSpatialSpectatorPartition.lean:75` | Original partition pin and cap |
| `common_quadratic_response_ratio` | `RationalCommonQuadraticResponse.lean:143` | Justified shared-factor cancellation |
| `localResponseFloor`, `localResponseFloor_positive`, `localResponseFloor_le_window` | `BF4ExactSlabFixedSpatialLocalResponse.lean:69`, `BF4ExactSlabFixedSpatialLocalResponse.lean:75`, `BF4ExactSlabFixedSpatialLocalResponse.lean:82` | Explicit positive witness and actual finite normalized response |
| `centered_window_response_floor`, `connected_response_floor` | `BF4WilsonAllNomeLocalConnectedFloor.lean:83`, `BF4WilsonAllNomeLocalConnectedFloor.lean:133` | Original mean and existing cutoff/time limits |
| `faceExcitation_response_floor`, `padded_faceExcitation_response_floor` | `BF4WilsonAllNomeLocalConnectedFloor.lean:163`, `BF4WilsonAllNomeLocalConnectedFloor.lean:173` | SAME completed vector/time; padding discharges activity |

## Remaining boundary and next useful work

The earlier width-dependent floor obstruction does not apply to c(w): that
obstruction bounded a different, explicitly width-dependent coefficient.
This theorem does not refute any existing fringe time-kernel result; an
inactive face is excluded, and strict padding changes the original width.
There is no asserted time-intertwining isometry between those carriers.

The all-nome fixed-width cutoff/time carrier exists, but a corresponding
all-nome thermodynamic family with its original observable comparisons and
moduli is still missing. Existing spatial-union consumers retain their
small-nome guards. A nome-only response floor does not remove those guards
or establish survival on a spacing family. The useful signed original-action
spatial/scaling estimate, same-object OS/scaling identification, finite
physical-mass calibration, full continuum QFT axioms and every-group target
remain open. Resume the actual signed/scaling producer; do not add further
generic normalization or completion wrappers in place of that estimate.

## Verification and parallel work

Nine final focused serialized one-worker checks passed 31 printed axiom
gates, all within {propext, Quot.sound}. No full-root/full-tree build,
global axiom audit or frontier guard was run. No sorry, custom axiom or
new open analytic estimate was introduced; no existing sorry was closed.
Root imports are registered but no root compilation is claimed.

Final logs under `/tmp/` are `ym-kinetic-positive-order-20260930.log`,
`ym-spectator-transmission-20260930.log`,
`ym-physical-spectator-transmission-20260930.log`,
`ym-spectator-moments-20260930.log`, `ym-common-quadratic-20260930.log`,
`ym-spectator-partition-20260930.log`, `ym-spectator-dual-20260930.log`,
`ym-local-response-20260930.log`, and `ym-local-connected-floor-20260930.log`.

Sol supplied transmission, moments, partition and limit joins; Luna supplied
rational cancellation and traced downstream consumers. Root proved positive
quadratic order, the actual face transmission and normalized response join.
An independent source review checked denominator identity, full exterior
retention, active-edge guards and parameter scope. The safe-build skill kept
all verification focused, serialized and capped at 20 GiB with 12 GiB OS
reserve. Corrected checks finished in their initial calls; no long-job
polling was needed. Continuous safety telemetry remained enabled.
