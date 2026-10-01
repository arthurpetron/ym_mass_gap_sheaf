# Whole signed family response against original variance

Date: 2026-10-01 UTC. The whole signed spatial plaquette family now has
a strict finite energy ceiling against its SAME original interacting
variance. The coefficient is explicit and independent of spectator volume,
late cutoff and positive terminal depth. Physical scaling and the Clay
target remain open.

## Actual source and coefficient

For a strictly padded family qs with arbitrary rational coefficients, let
f=spatialSpan(width,c,qs), g=u_(n+1), q=V*g, and P be the ORIGINAL active
product heat. The density is q*Pq=V*u_(n+1)*u_(n+2), so its odd marginal
depth is n+1, not n. Its mean is computed from this density and the original
partition Z. No fringe projection or replacement probability law is used.

Let m=|qs|. The existing size-only local band supplies

    l = localLower(w,4*m) = headFloor(w)^(28*m),
    u = localUpper(w,4*m) = prefixCap(w)^(28*m),
    lambda = w^12,
    rho = lambda*l^2/u^2 > 0.

The hypotheses are 0<w<1, K>=headCutoff(w), K>=1, strict spatial padding,
all faces in the smaller slice, and terminal depth n+1. Faces may repeat;
coefficients may have either sign. Fixed or bounded family-list size is
necessary for a common coefficient. Neither beta nor physical spacing is
calibrated here. Nome dependence is explicit, not uniform in coupling.

## Constructed dual and zero case

`family_spectator_kinetic`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyLocalBand.lean:259`,
proves P(R*f)=lambda*(PR)*f under every supported Haar test, with one common
R retaining the complete previous message and exterior factors.
`family_spectator_zero`, same module line 315, proves H[R*(PR)*f]=0.
It erases one independent link only inside a proved Haar equality; no
factor is dropped from the stated source or density.

For the actual center c, set psi=f-c and t=R*(f-lambda*c). The proved image
is Pt=lambda*(PR)*psi. With W=R*(PR), define

    F=H[W*psi^2], M=H[q*(Pq)*psi^2],
    C=H[(q*psi)*Pt], B=H[(q*psi)*P(q*psi)], D=H[t*Pt].

Actual positive certificates give C>=lambda*l*F, M<=u^2*F and
D<=lambda*F. The last estimate uses the zero first moment and lambda<=1.
Sharp kinetic Cauchy--Schwarz gives C^2<=B*D. Thus lambda*l^2*M<=u^2*B.
When F>0 the scalar cancellation is by lambda*F>0. When F=0 the original
M is zero by its upper bound and positivity. No reciprocal of variance,
source or spectator mass is formed.

Evidence is `response_cleared`,
`lean/YMGap/Continuum/PositiveDualBandScalar.lean:61`, and
`response_band_cleared`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatBandResponse.lean:240`.
`sourceProductUpper`, same module line 87, constructs the actual upper
density certificate rather than assuming it.

## Original energy and variance join

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean`.
`oddMoment_unprojected_source`, line 77, identifies every source moment
with the unchanged odd marginal. `centered_unprojected_square`, line 95,
proves M=Z*Var_odd(f) at the actual original mean. `energy_shifted`, line
130, proves that centering leaves the original energy unchanged, using
its full two-slice jump and the actual edge density.

`padded_family_energy_band_cleared`, line 180, supplies all original
geometry and certificates and proves

    u^2*E_original + lambda*l^2*(Z*Var_odd) <= u^2*(Z*Var_odd).

`padded_family_energy_band`, line 243, divides only by the explicit
positive scalar u^2 and proves E_original<=(1-rho)*Z*Var_odd.
`familyResponseFraction` and `familyResponseFraction_positive`, lines
165 and 171, return rho and its positivity. Squaring is performed on the
complete signed family throughout; no off-diagonal term is discarded.

## Remaining scaling input

This supplies a finite quantitative fraction, not a scaling-small energy
ceiling. The local source floor can deteriorate as w approaches one or
family size grows; nothing here proves rho approaches one. The primary
survival input still needs a useful energy/variance rate on a justified
physical observable and spacing family. Existing complete signed Ward and
channel identities remain available for that estimate. Additional equivalent
finite-band wrappers would not discharge this missing analytic input.

Uniform physical decay, mass calibration, nontrivial continuum survival,
same-theory continuum OS/QFT structure and every compact simple group remain
open. No canonical frontier field or displayed chart state changed.

## Verification

Four final focused checks passed all 28 printed gates within
{propext, Quot.sound}; the footprint definition is axiom-free. No new sorry,
axiom, Classical dependency, native_decide or noncomputable declaration.
Independent Sol and Luna source reviews checked the scalar cancellation,
zero case, signed terms, source depth and physical-scaling limitation.

Only main compiled, serially using the monitored launcher with one worker,
20 GiB ceiling, 12 GiB OS reserve and dynamic telemetry. The separate
sign-test draft hit the kernel memory cap and is NOT part of this accepted
result. Subsequent process inspection found no surviving compiler or runner,
and memory pressure reported 78 percent free. No safety limit was raised.
Namespace and elaboration errors were repaired by explicit imports and
typed opaque endpoints before acceptance.

Root imports were registered but not checked as an aggregate. No full root
build, tree audit or guard was run. CI remains manual-only. The documentation
skill kept finite control distinct from its open scaling consumer; the
unchanged ASCII chart was not reprinted.

Final log SHA-256 values under `/tmp/`:

- `ym-positive-dual-band-scalar-final-20261001.log`:
  `8a1fa136a684818af193070e36533816c64a006df6beffe5d8d4d9bf4b148794`.
- `ym-product-heat-band-response-final-20261001.log`:
  `f096398b0ae0c10f5d32387fcdd3cd56d515e54f8d8235aaf737020b629b1cd5`.
- `ym-family-local-band-final-20261001.log`:
  `2497759e01e0db9dc8efb9021ac8b9aa86f33892ba021cda4c80d3ef77acfde3`.
- `ym-family-band-response-final-accepted-20261001.log`:
  `3328fcb235cbf0d66e1e1dcc00e6506da7b49f1c8441dec14048145e81146dbd`.

## Addendum: a generic spectator heat-retention comparison is false

The proved band-response theorem above is unchanged. This addendum checks
a DIFFERENT proposed use of local bands: replacing the FULL-width source
cap/floor in the bare-source first-order bound with a selected-footprint band.
That argument must not silently identify bare spectator square with the
spectator's original heat pairing. No such terminal estimate is supplied here.

All new declarations are in
`lean/YMGap/Continuum/SU2QuaternionSpectatorHeatRetentionFence.lean`.
The seed is the existing positive q=1+chi_2/4 and the ORIGINAL one-link
`heatAt 0 1 half 3`. `pairingSeed_mass_pin`, line 153, proves its paired
integral is exactly the existing sourceMass(q)=H[q*Pq]. The source is the
same at both endpoints, not an auxiliary law substituted into a YM claim.
`sourceSeedCertificate` and `pairingSeedCertificate`, lines 137 and 140,
supply polynomial positivity. `sourceSeed_square_value` and
`pairingSeed_value`, lines 149 and 160, give 17/16 and 4097/4096.

`pairProduct`, line 58, places independent copies on literal interleaved
block pairs (0,1),(2,3),.... `haar_pairProduct`, line 102, proves exact
ordered Fubini. `pairProduct_mul`, line 88, pins the duplicated source in
the heat integrand. The heat product and both sources remain explicit in
`pairedMass`, line 172; this is not a scalar or character-diagonal surrogate.
`spectatorCertificate` and `pairedDensityCertificate`, lines 175 and 178,
return the positivity data on every finite enlarged carrier.

`bareMass_value` and `pairedMass_value`, lines 184 and 190, prove

    bareMass(m) = (17/16)^m,
    pairedMass(m) = (4097/4096)^m.

`pairedMass_positive`, line 197, proves the latter is positive.
`escapeExponent`, line 237, computes m(C)=17*C.num.toNat+1 for C>=0.
`ratio_escapes`, line 239, uses the existing constructive numerator bound
and Bernoulli inequality: (17*n+1)*(255/4097)>n>=C. The exact per-copy
ratio is 4352/4097>1. `retention_failure`, line 280, proves

    C*pairedMass(m(C)) < bareMass(m(C)).

`retentionCounterexample`, line 293, returns the extent and its proof as
Type-level data. `no_uniform_heat_retention`, line 297, excludes ANY fixed
nonnegative comparison constant for this actual independent-heat family.
No reciprocal of the spectator mass is used.

`outsideSpectator_independent`, line 206, proves independence of EVERY
block in ANY fixed selected footprint. `outsideSpectatorCertificate`, line
210, carries positivity to that placement. `outsideBareMass_pin` and
`outsidePairedMass_pin`, lines 221 and 226, prove both masses unchanged;
`outside_retention_failure`, line 303, transports the violation. Therefore
adding selected-footprint independence does not repair the generic inference.

These sources are NOT identified with the original 4D terminal recursion,
and are NOT claimed independently vertex-gauge-invariant. The theorem does
not refute an estimate using those additional physical properties, the
existing full-width `family_firstOrder_variance_bound`, or the whole-family
band-response theorem. It is not a Yang--Mills counterexample. The consumer
is pruning a proposed positivity/independence-only local replacement of the
source comparison, rather than adding an assumed analytic field.

The next proposed producer is a first-order/SAME-variance bound within the
EXISTING exact passive-channel energy expansion. The checked declaration
`SU2QuaternionProductHeatPassiveChannels.sourceEnergy_projected_channels`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPassiveChannels.lean:252`,
already retains spectator heat at its original nome and cutoff through
computed Gram channels. Its first-order sum still needs an exact weighted
channel-square/spectator-pairing pin and quantitative bound against original
centered Z*Var. These are unproved next estimates, not a source replacement
or a claimed physical scaling estimate. Actual selected cutoff debt remains.

An API distinction matters: existing subset productMap integrates ALL lower
slots, including those absent from its kernel list. In particular
`SU2QuaternionProductHeatMarginals.productMap_nil`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:84`, returns a
Haar constant, not the input polynomial. Thus naive composition of subset
productMap is NOT an identity-on-selected/spectator-only operator. Reuse
the proved channel decomposition instead of assuming that false operator
equality. The finite w=1 selected kernel is also a cutoff projection, not
an identity on every polynomial; original omitted-mode debt may not be erased.

The final focused check exited zero with all 25 printed gates within
{propext, Quot.sound}; pairProduct and escapeExponent are axiom-free.
Independent Sol reviewed the source pins, heat eigenvalue, Fubini, explicit
extent and scope; Luna located the constructive growth APIs. Namespace,
carrier-order arithmetic and elaboration errors were repaired without
changing mathematical hypotheses or raising memory/heartbeat limits.
Only main compiled, serialized through the safe launcher with one worker,
20 GiB ceiling and 12 GiB OS reserve. Preflight found no competing process,
84 percent pressure-free capacity and zero swap. No new sorry, axiom,
Classical dependency, native_decide or noncomputable declaration. Root
registration is not aggregate verification; no root/tree/audit/guard ran.
CI remains manual-only. No canonical frontier field or chart marker changed.

Final log: `/tmp/ym-spectator-retention-fence-outside-final-20261001.log`.
SHA-256: `7c1cde5d18caf60b4c8430473a52c864049b8097d64dfbaf3d6a52714b231bd7`.

## Addendum: weighted channel monotonicity on the original kernel

The weighted conditional-kernel pin mentioned above ALREADY existed as a
private theorem; exporting it is not new mathematics. New source-order and
scaling lemmas now supply the kernel-level local-band producer, rather than
another energy-decomposition wrapper. All declarations in this addendum are
in `lean/YMGap/Continuum/SU2QuaternionFamilyHeatGramPositiveWeight.lean`.

For passive ids, write b_c(p)=familyProject(ids,p*c), cs=the ORIGINAL
productChannels(n,w,K,ids), and

    C_p(e)=sum_(c in cs) rho_c * H[b_c(p)^2 * e].

The weight e is supported on the n-block carrier and independent of every
passive id. `weighted_cross_pin`, line 83, proves C_p(e) equals

    H_(2n)[productHeat(ids) * p * swap_ids(p) * e].

Passive variables are copied; unselected variables remain SHARED. This is
not the repository's subset productMap. No positivity hypothesis is needed
for this exact identity. The polynomial e need not have independent square
generators, and signed channel polynomials are retained.

NEW `productChannels_familyProject_positiveWeighted_square_mono`, line
136, requires 0<w<1, K>=headCutoff(w), distinct physical ids, support and
WHOLE positive-polynomial certificates P,Q,E for p,q,e, plus D for q-p.
It proves C_p(e)<=C_q(e). The short positive two-copy certificate is

    productHeat * [(q-p)*swap(q) + p*swap(q-p)] * e.

Its exact polynomial expansion is the upper kernel square minus the lower
one. Extension and reindexing transport each existing certificate; Haar
nonnegativity and the weighted kernel pin give the result. No normalization,
source mass or variance is inverted. No positive sign is assigned separately
to the channel polynomials, and no absolute coefficient budget is introduced.

NEW `productChannels_familyProject_weighted_square_smul`, line 199, proves
C_(c*p)(e)=c^2*C_p(e) for ANY rational c. It needs only the support,
independence and channel-index conditions of the algebraic pin, not a
positive c or a heat-floor hypothesis. Consequently a supplied local upper
band q<=u*R can be used with the exact coefficient u^2, while keeping the
SAME spectator heat and selected weight. This is a generic cone consequence,
not yet an actual-terminal/SAME-variance theorem.

The intended physical consumer remains l^2*A_ch<=12*u^2*Z*Var for the
complete signed/repeated spatial family at the ORIGINAL odd-marginal mean.
A_ch is the channel-weighted first-order angular sum, distinct from the
old raw A=H[q^2*Gamma(f,f)]. Its actual producer still needs terminal-band
transport through justified fringe projection, exact physical selected/passive
partition and common-spectator moment pins, and the whole-family Gamma/Haar
factorization. The old full-width raw A bound is unchanged. The existing
channel energy/Taylor consumer must retain its actual signed cutoff and
remainder debt. No useful scaling-small rate, continuum survival, physical
mass, full same-theory QFT or every-group conclusion follows yet.

The final focused check exited zero with all four printed gates EXACTLY
{propext, Quot.sound}, including the unchanged Bessel-contraction theorem.
Independent Luna source review confirmed the difference factorization,
whole-weight certificates, c^2 coefficient and parameter scope. No sorry,
new axiom, Classical dependency, native_decide or noncomputable declaration.
No memory or heartbeat limits were raised. Only main compiled, serialized
through the monitored one-worker 20 GiB launcher with 12 GiB OS reserve.
Initial preflight for this sequence found no competing process, 84 percent
pressure-free capacity and zero swap. No root/tree/audit/guard ran. CI and
canonical fields/chart are unchanged; the ASCII chart was not reprinted.

Final log: `/tmp/ym-weighted-channel-mono-20261001.log`.
SHA-256: `d16f084bb76fcbcd5f3f1b37d312393d47d108d09c810fa39496ecf2d5d7e21b`.
