# Complete signed-family angular cost against the SAME interacting variance

Date: 2026-10-01 UTC. PROVED supporting estimate after `2d9577d`.
This is an actual original-action finite instance, not an assumed analytic
interface, a complete signed-energy scaling bound, or continuum closure.

## Mathematical advance

Let F=sum c_p*f_p be the COMPLETE signed spatial plaquette family, including
repeated faces. Its deduplicated literal link footprint is J. Set

    W = V*g_n*g_(n+1),
    Z = oddMass(w,K,width,n),
    Vc = Z*oddVariance(F),
    C(w) = 6*relativeCap(w,4096)+2*relativeCap(w,32).

The same-weight Young square at each of the six planes of each J-link gives

    -2*Ward(F) <= 6*|J|*C(w)^2*Vc + Angular(F).

Outside J the derivative of F is coefficientwise zero. No independence of W
is required and no source factor is removed. The existing actual four-link
Casimir identity gives Angular(F)+Ward(F)=12*Vc, hence

    Angular(F) <= (24+6*|J|*C(w)^2)*Vc,
    |J| <= 4*qs.length.

After dividing ONLY by SAME positive Z, the original normalized angular
energy is bounded by (24+24*qs.length*C(w)^2)*oddVariance(F).
No variance lower bound or inverse density floor is used. Every family cross
term remains inside the same squared F and its own interacting variance.

The original temporal-energy consumer is therefore

    normalizedEnergy(F) <= (1-w)*(24+24*qs.length*C(w)^2)*oddVariance(F)
                            + normalizedRemainder(F).

The COMPLETE signed normalizedRemainder, including the angular-weight defect,
mixed pair remainder and diagonal pair remainder, is unchanged. No sign,
smallness or favorable cancellation of that remainder is assumed.

## Causal declaration chain

1. `lean/YMGap/Continuum/QuaternionHaarLocalRelativeWard.lean:57`,
   `block_residual_lower`, generalizes relative Young to an arbitrary original
   in-range quaternion block. It does not require head-linearity.
   `active_residual_lower` (:148) sums the literal block list and charges
   only its length; repeated blocks, if supplied, are counted.
2. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyFootprint.lean:72`,
   `familyObservableBlocks_length_le_four`, proves the deduplicated physical
   footprint has at most four slots per listed face, including repeated faces.
   `familyObservableBlocks_active_after_padding` (:116) proves each is active
   at every strictly larger width. `linkAt` (:127) computes the physical link
   with getElem, and `linkAt_idxOf` (:149) proves its original first-occurrence
   index. The existential face link is used ONLY in this Prop equality proof,
   never extracted into the Type-valued selected link or score certificate.
3. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRelativeWard.lean:193`,
   `familyBlockRelativeBound`, constructs the actual marginalRelativeBound at
   every J-link. It keeps W=V*g_n*g_(n+1) and the existing score cap C(w).
4. `family_angular_variance_cleared` in that module (:215) removes zero spectator
   residuals and energies through the proved permutation of the original block
   list. The existing `marginal_centered_square`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilySourceVarianceBound.lean:150`,
   identifies the actual centered square as Vc. The existing `family_ward`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:124`,
   supplies Casimir 12 on this SAME signed family and original marginal.
5. `family_angular_variance_length_cleared` (:261) proves nonnegativity of Vc
   with the actual marginal square certificate, then applies the footprint
   count. `familyLengthAngularVarianceFactor` (:144) computes its coefficient
   as 24+6*ofNat(4*qs.length)*C(w)*C(w), independent of width/depth/cutoff.
   `family_normalized_angular_variance` (:311) cancels only SAME positive Z.
6. `padded_family_energy_relative_ward` (:332) consumes the existing exact
   `padded_family_normalized_taylor`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalTaylor.lean:138`,
   retaining the complete signed normalized remainder and its original law.

## Parameters and unresolved analytic input

Guards: 0<w<1; K>=endpointRelativeCutoff(w); base<width; all listed faces in
spatialFaces(base). Coefficients are arbitrary rationals; zero coefficients,
empty lists and repeated faces require no positive-variance assumption.
The cutoff onset and C depend explicitly on nome. The length envelope has
no width, terminal-depth or later-cutoff parameter. The existing source of
relativeCap is relativeCost+1, with relativeCost=d*JacobiShiftedRelativeSlope.budget.
No near-one uniform or useful physical-scaling bound for this coefficient is
proved. A count independent of width for a fixed list is not uniform control
over growing observable families.

This closes the direct finite angular/SAME-variance producer for whole families,
not the PRIMARY useful COMPLETE signed temporal-energy/SAME-variance scaling
input. NEXT is control of the JOINT budget, exploiting actual signed source/
remainder structure on a justified changing-coupling/spatial/spacing family.
The new score envelope is an available comparison, not permission to assume
its calibration or replace the signed remainder by an absolute source cost.

No completed angular-output or remainder limit, changing-width map, physical
time/mass calibration, nonzero continuum survival, full continuum OS/QFT,
field/short-distance identification or every-compact-simple-group instance
is constructed. Those obligations remain OPEN. No canonical displayed claim
changes; the unchanged ASCII chart is not reprinted.

## Verification and independent review

All THREE accepted focused checks exited zero and emitted target oleans.
Their 2+8+7=17 printed gates contain three empty axiom sets and fourteen
exactly {propext, Quot.sound}. Final sources introduce no sorry, new axiom,
Classical dependency, native_decide, noncomputable declaration, analytic field
or weakened frontier. Two mathematical reviews and an independent final
source/log review passed.

One intermediate footprint check compiled but FAILED the axiom gate because
its index proof inherited Classical.choice. That draft and its log were not
accepted. The final proof instead uses a computed first-occurrence index and
does not depend on baseLinks_nodup or idxOf_lt_length_iff. Missing namespace,
explicit derivative-index and expression-syntax errors were also repaired
before acceptance. Failed logs do not certify a milestone.

Main alone compiled through the safe-build skill and monitored launcher:
one worker, 20 GiB ceiling, unchanged 12 GiB OS reserve and dynamic telemetry.
Preflight found 84 percent pressure-free memory and zero swap. Separate
user-owned reliability-study jobs were left untouched; no competing Lean,
Lake, pytest or runner was found. Final swap remained zero. No worker,
memory or heartbeat limit was raised. No full-root/tree build, broad audit,
guard or CI change ran. Root imports are registered, not aggregate-checked.
The historical progress-metric script calls a broad guard and was not run.

Accepted logs and SHA-256:

- `/tmp/ym-local-relative-ward-second-20261001.log`:
  `d9b4fb6a9a6330dad699cf14707c540a20f7abfcad6b93aa84db6ad68181527d`.
- `/tmp/ym-family-footprint-third-20261001.log`:
  `43cc8993b8349014575d232adae7c26e1cba0b1432cdfc3bda622b09885fcb38`.
- `/tmp/ym-original-family-relative-ward-second-20261001.log`:
  `7781f47e54de2e9b5cb2c570342678bc01365d200db3ee066745dffd67f8fd90`.
