# Local angular budget under the ORIGINAL signed-family marginal

Date: 2026-10-01 UTC. PROVED supporting estimate after `1167dc2`.
This is an actual finite original-action angular producer and energy consumer,
not a supplied analytic interface or a continuum/SAME-variance scaling proof.

## Mathematical advance

For a Nodup spatial face list qs with arbitrary rational coefficients, let
F=sum c_p*f_p, where each f_p is the literal fundamental plaquette trace.
Each actual physical link belongs to at most six distinct literal faces.
For ANY common certified positive Haar weight W, local finite Cauchy gives

    H[W*Gamma(F,F)] <= 6*sum_p H[W*Gamma(c_p*f_p,c_p*f_p)].

All complete-family cross terms remain inside Gamma(F,F). Only derivatives
off the actual block-face row vanish; neither weighted independence nor zero
cross-covariance is inferred. Each actual four-link trace satisfies
Gamma(f_p,f_p)=4*(4-f_p^2) in the original Haar carrier, so

    normalized_W[Gamma(F,F)] <= 24*sum_p c_p^2*normalized_W[4-f_p^2].

This removes a family-size or spatial-volume MULTIPLIER from the angular
budget. The coefficient-square sum can still grow with the observable family.
The same arbitrary W remains; no spectator source factor is removed.

## Causal declaration chain

1. `lean/YMGap/Continuum/QuaternionHaarLocalAngularFamily.lean:112`,
   `masked_square_certificate`, pads the filtered nonzero derivative row to
   its explicit count bound D with zero polynomials. The existing finite
   square certificate returns SOS data for D*sum squares minus square of sum.
   Empty rows and D=0 require no division or positive-variance assumption.
   `local_plane_certificate` (:183) applies derivative linearity.
   `weighted_blockGamma_local_family` (:312) sums the six actual planes.
   `weighted_activeGamma_local_family` (:368) sums actual blocks and uses
   finite Fubini. `weighted_finitePolySum_activeGamma_local_family` (:429)
   matches the literal signed spatialSpan expression exactly.
2. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyIncidence.lean:36`,
   `blockRow`, computes incident physical links with their actual baseLinks
   index. `blockRowFaces_length_le_six` (:66) uses index injectivity and the
   existing complete six-plaquette star enumeration. It requires qs.Nodup,
   not a bound on width. `blockRow_derivative_zero` (:116) proves the literal
   face trace's angular generators vanish coefficientwise off that row.
3. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyLocalAngular.lean:117`,
   `weighted_spatial_family_angular`, supplies D=6 and actual support/locality.
   `normalized_spatial_family_angular` (:169) uses bilinear scalar homogeneity
   and the existing `plaquette_gamma`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCurvature.lean:129`.
   Six is charged once; the full four-link Gamma pin contributes four.
4. `localAngularBudget` in the new physical module (:204) computes

       C_local=24*sum c_p^2*(4-middleRatio_(n+1,n)(f_p^2)).

   `family_normalized_angular_le` (:238) supplies the ACTUAL original marginal
   W=V*g_n*g_(n+1), its constructed marginalCertificate, and its SAME positive
   oddMass. Existing `marginalMoment_pin`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:64`,
   identifies every squared-face moment with the original middleRatio.
   The angular square is exactly marginalAngular, not source-q^2 energy.
5. `family_ward_local_budget` in the new physical module (:270) uses the
   existing SAME-law identity A+Ward=12*Var to prove 12*Var-C_local<=Ward.
   This comparison assigns no sign to the complete derivative-of-weight term.
6. `padded_family_energy_local_angular` in that module (:293) consumes the
   original exact `padded_family_normalized_taylor`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalTaylor.lean:138`:

       normalizedEnergy(F) <= (1-w)*C_local+normalizedRemainder(F).

   The complete signed remainder is the mixed pair remainder minus diagonal
   pair remainder minus (1-w)*angularWeightDefect, all divided by SAME Z.
   It is neither dropped nor subtracted twice. Strict padding supplies the
   actual fringe independence; spatial membership is transported to the
   larger literal slice, not assumed for an unrelated carrier.

## Parameters, scope and remaining input

The constants 6 and 24 do not depend on nome, heat cutoff, width, terminal
depth or family size. This says nothing about uniformity of the actual face
moments or signed remainder in those parameters. Original instances require
0<w<1 and K>=headCutoff(w); Taylor additionally requires strict spatial padding.
No beta/spacing calibration or completed map between widths is constructed.

Repeated faces are allowed in the generic row-count theorem but count as
separate occurrences. The physical six-incidence statement requires Nodup:
m copies of the same face can have an m^2 angular square, not an m cost.
The proof does not silently consolidate repeats or weaken general-family fields.

The next useful input is control of the JOINT original budget
(1-w)*C_local+normalizedRemainder relative to SAME signed interacting variance
on a justified changing-coupling/spatial/spacing family. Individual cap deficits
are not the family's centered variance; no such comparison is proved here.
Existing conservative variance floors do not automatically calibrate this bound.
Nontrivial continuum survival, spatial/spacing control, physical time/mass,
full SAME-theory continuum OS/QFT, field/UV identification and all compact
simple groups remain OPEN. No canonical displayed proof node changes.

## Focused verification and independent review

All THREE accepted focused checks exited zero and emitted target oleans.
The 5+6+6=17 printed gates each depend exactly on {propext, Quot.sound}.
No new source sorry, axiom, Classical dependency, native_decide,
noncomputable declaration, analytic field or weakened frontier was introduced.
Initial namespace, scalar-equivalence orientation and explicit-target
elaboration errors were repaired before acceptance; failed logs are not evidence.

Independent mathematical review checked local occurrence counting, SOS padding,
signed cross terms, the 6*4 constant, SAME marginal normalization, Ward direction
and the complete original remainder. Independent source/log review checked
all gate names/dependencies and accepted hashes. Reviewers ran no compilers.

Main alone used the safe-build skill and monitored launcher with one worker,
20 GiB ceiling, unchanged 12 GiB OS reserve and dynamic telemetry. Preflight
found 84 percent pressure-free memory and zero swap; separate user-owned
reliability-study jobs were left untouched. No hardware or heartbeat limit
was raised; final swap usage remained zero. No full root/tree build, broad
audit or guard was run. Root import
registration is not aggregate verification. CI remains manual-only.

Accepted logs and SHA-256:

- `/tmp/ym-local-angular-family-fourth-20261001.log`:
  `ec6731ab22371108aa093ee580d29b4803fb3b01939edd67ca8168386a2411c0`.
- `/tmp/ym-spatial-family-incidence-second-20261001.log`:
  `793d329d0b4b822dae81689eeeb1520e8620aca4cc979682d44ebef9deb25d35`.
- `/tmp/ym-original-family-local-angular-third-20261001.log`:
  `184b7f553bf04be79422ab0cf3ef4d52cfb82ed70efa9526562e3eee177df1d3`.
