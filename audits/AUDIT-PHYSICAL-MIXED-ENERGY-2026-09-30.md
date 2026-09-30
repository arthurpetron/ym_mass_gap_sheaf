# Physical two-edge transport and signed-source mixed energy

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS. The previously missing physical two-edge join
is supplied, and the selected original action has an actual signed-source
mixed-energy lower bound. This is not yet a variance or transfer estimate.

## The same physical source throughout

For an actual corrected-slab face p, its physical edges A and B are pinned
to the first two exposed blocks by the existing `faceExposure`. Both
derivatives pass through that SAME finite block-swap chain. The padded
representatives are compared by Haar-carrier equality, not an invalid raw
coefficient equality.

The physical operator differentiates at B first, then A. Summing its
36 squared angular directions gives

    physicalMixedSquare(f_p) = 8 + f_p^2

under every polynomial insertion on the unchanged full Haar carrier.
It is the same `mixedDerivative` used by the signed-source isolation
theorems from the preceding checkpoint.

Source map:

- `QuaternionHaarBlockAngularCarrier.reindex_blockAngularDerivative_carrier`,
  `lean/YMGap/Continuum/QuaternionHaarBlockAngularCarrier.lean:49`.
- `QuaternionHaarMixedAngularTransport.chain_mixedSquare` and
  `oriented_word_mixedSquare_of_exposure`,
  `lean/YMGap/Continuum/QuaternionHaarMixedAngularTransport.lean:149`, :195.
- `BF4ExactSlabPlaquettePhysicalDerivativeCarrier.linkDerivative_carrier`
  and `mixedDerivative_carrier`,
  `lean/YMGap/Continuum/BF4ExactSlabPlaquettePhysicalDerivativeCarrier.lean:46`, :95.
- `BF4ExactSlabPlaquetteMixedSquare.physicalMixedSquare_carrier`,
  `fullSlabFaceCharacter_mixedSquare`, `physical_face_mixedSquare`,
  and `physical_face_weighted_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabPlaquetteMixedSquare.lean:68`, :82, :104, :113.

## The original signed sum, not independent plaquette variances

Let F=sum_q c_q f_q, over a duplicate-free physical face list containing p.
Every coefficient is rational with arbitrary sign. For every rational m,
the new exact identity is

    physicalMixedSquare(F-m) = c_p^2 (8+f_p^2).

The original coefficient-isolation theorem and the physical mixed-square
identity are now actually composed. For any constructed positive weight W,

    H[W*physicalMixedSquare(F-m)] >= 8*c_p^2*H[W].

The actual selected physical heat action supplies W's certificate for
0<w<1 and K>=headCutoff(w). Choosing the entire physical face-ID list
gives the full action. No independent-face law, surrogate completion,
absolute-coefficient sum, or global density minimum is substituted.

Declarations in `lean/YMGap/Continuum/BF4ExactSlabSignedMixedEnergyFloor.lean`:
`affine_mixedSquare_isolates` at :54, `affine_mixedSquare_identity` at :90,
`affine_mixed_energy_floor` at :101, and
`selected_action_mixed_energy_floor` at :117.

The number eight is an SU(2) kinematic coefficient. Its independence of
coupling does NOT assert a coupling-independent variance or mass gap.
The inequality controls a mixed derivative energy, not the source norm.
The center is arbitrary; no particular mean is assumed or silently chosen.

## Original one-edge upper bound

`BF4ExactSlabSignedSourceRelativeEnergy.signed_source_one_edge_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabSignedSourceRelativeEnergy.lean:253`, supplies
the first upper estimate under the full original physical-face action:

    H[W*Gamma_link(F)] <= M(w)*H[W*(F-m)^2],
    M(w) = 24+36*(6*relativeCap(w,2048))^2.

Both sides are expressed in the same selected-link head frame. The exact
nonincident predictor is retained; `centered_error_carrier` at :226 identifies
its error with the literal whole centered source under every insertion.
The cutoff guard is `QuaternionHaarHeatRelativeAngularBound.relativeCutoff
w 2048 <= K`, not the different retained-heat comparison cutoff.

This upper theorem uses the Nat-indexed `observable`, whereas the lower
theorem uses the plaquette-indexed `affineSource`. Their original face
polynomials agree in meaning, but an exact encoding pin is still required
before composing these particular statements. No such join is assumed here.

## Remaining quantitative join

The missing direction is an upper bound for this SAME mixed energy by the
SAME centered source norm. The existing original relative Ward factor is
M(w)=24+36*(6*relativeCap(w,2048))^2. The first application is now supplied.
A second application must retain the
incident/free decomposition after the first derivative, or prove the
corresponding degree-at-most-one polynomial estimate and its stability
under differentiation at another block.

The proposed result 8*c_p^2*Z <= M(w)^2*H[W*(F-m)^2] is still OPEN.
Even after proving it, summing it would cost the number of faces. A genuine
bounded-interference/dual-family argument is needed for a support-uniform
signed Gram bound. No family-size-independent result follows from the
coefficient detector alone.

SAME literal completed-carrier realization, controlled physical support,
nontrivial scaling survival, useful every-state decay, physical mass
calibration, full continuum QFT and every-group requirements remain OPEN.
No canonical chart field changes.

## Verification

Focused monitored checks use one worker, a 20 GiB hard worker cap and
12 GiB OS reserve. Final logs: `/tmp/ym-block-angular-carrier-20260930.log`,
`/tmp/ym-mixed-angular-transport-20260930.log`,
`/tmp/ym-physical-derivative-carrier-20260930.log`,
`/tmp/ym-physical-mixed-square-20260930.log`,
`/tmp/ym-signed-mixed-energy-floor-20260930.log`, and
`/tmp/ym-signed-source-relative-energy-20260930.log`.
These six files passed 33 public axiom gates in {propext, Quot.sound}.

A trial exposed-word check hit Lean's reduction budget. Keeping the
differential operators opaque solved it; the final checks use the default
heartbeat budget, with no raised memory ceiling. No new sorry, axiom,
classical premise, assumed analytic bound or weakened frontier. No full
build, broad audit/guard, CI change or Rust computation. Sol supplied the
physical derivative comparison and the one-edge source decomposition;
Luna independently reviewed source/action
alignment and the energy-versus-variance boundary.
