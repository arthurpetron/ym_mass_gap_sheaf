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

## Addendum: actual channel first order against SAME original variance

The physical application proposed in the preceding addendum is now proved.
It bounds the CHANNEL first order in the existing original-energy expansion,
not the old raw Haar first order. No extent-uniform bare/heat spectator
retention assertion is used or assumed.

### Original objects and common-mass argument

Let N=|baseLinks(width)|, f=spatialSpan(width,c,qs), psi=f minus its ORIGINAL
odd mean at depth n+1, and q the original projected endpoint source at that
same positive depth. Let P be familySpectatorBlocks(width,qs), and let R be
the actual common family spectator at predecessor n, projected over the
unchanged fringe schedule. Define b_z(a)=familyProject(P,a*z) using the
unchanged productChannels(N,w,K,P) with weights rho_z. Set

    C_a(e) = sum_z rho_z H[b_z(a)^2*e],
    M_R = sum_z rho_z H[b_z(R)^2] >= 0,
    l = localLower(w,4*|qs|), u = localUpper(w,4*|qs|),
    G = Gamma_full(f,f), e = familyProject(P,G),
    A_ch = C_q(G).

The actual projected source has constructed l*R<=q<=u*R certificates:
`projectedFamily_lowerCertificate` and `projectedFamily_upperCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelVarianceBound.lean:133`
and `:161`. `projectedFamilySpectator_outside_passive` at `:116` proves the
independence needed for R; it is not assumed from a footprint diagram.

The generic declarations below are in
`lean/YMGap/Continuum/SU2QuaternionPassiveChannelMomentFactorization.lean`.
`spectator_channel_independent` at `:108` proves every b_z(R) is independent
of EVERY original block. `channelSquare_factor` at `:136` gives
C_R(e)=M_R*H[e]. `spectator_sourceMoment_factor` at `:214` gives
sourceMoment_full(R,psi^2)=M_R*H[psi^2]. Its passive-independence premise
for the insertion is essential. This is ORIGINAL full-heat sourceMoment,
not a replacement bare-channel variance.

`channelSquare_project_weight` at `:167` proves C_q(G)=C_q(e) by exact
Fubini. This avoids falsely assuming literal syntactic independence of
zero-coefficient derivative terms in G. The whole projected SOS certificate
supplies positivity of e. The existing signed-family bare Haar Casimir pin
and shift inequality give H[e]=H[G]=12*H[f^2]<=12*H[psi^2], at the actual
original mean. Weighted source order and exact u^2 scaling therefore yield
A_ch<=12*u^2*sourceMoment_full(R,psi^2).

For the lower direction, `sourceMoment_square_mono` at `:259` and
`sourceMoment_smul` at `:241` give
l^2*sourceMoment_full(R,psi^2)<=sourceMoment_full(q,psi^2)=Z*Var_original.
Combining the two inequalities cancels NO mass or variance by division:

    l^2*A_ch <= 12*u^2*Z*Var_original.

`family_channel_firstOrder_variance_cleared` at `:198` and
`family_channel_firstOrder_variance_bound` at `:326` of
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelVarianceBound.lean`
supply these two final statements. `channelFirstOrderVarianceConstant`
at `:313` returns the explicit positive coefficient C=12*u^2/l^2 as data,
dividing only by the constructed positive scalar l^2.

### Actual original-energy consumer and open residue

`familyChannelTaylorDebt`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance.lean:107`,
is the signed channel sum of pairRemainder(b_z,b_z*f^2) minus
pairRemainder(b_z*f,b_z*f), at ORIGINAL w,K and the complete block list.
`padded_family_channel_energy_taylor` at `:119` proves the exact identity
E_original=(1-w)*A_ch+D_ch. `padded_family_energy_le_channelVariance` at
`:167` and `padded_family_normalizedEnergy_le_channelVariance` at `:189`
give its unnormalized and SAME-positive-partition normalized consumers:

    E_original/Z <= (1-w)*C*Var_original + D_ch/Z.

For the variance comparison, assumptions are 0<w<1, K>=headCutoff(w),
strict spatial padding, all faces in the smaller slice, and positive depth
n+1. Coefficients may have either sign; repeated and zero/empty families
are retained. C depends only on nome and family-list size, not full width,
late cutoff or positive depth. NO boundedness as w approaches one or family
size grows is claimed. The signed debt contains actual omitted finite-cutoff
modes and has neither an asserted favorable sign nor scaling smallness.

NEXT: jointly estimate that debt on a justified physical scaling family.
The existing Casimir-12 retained-square producer accepts signed channel
sources and can sharpen it, but signed curvature and cubic/omitted-mode
errors still require SAME-variance control. Spatial/spacing-uniform decay,
nontrivial continuum survival, physical mass calibration, full QFT and
every compact simple group remain OPEN. No canonical chart state changes.

### Verification and review

Three final focused file checks exited zero, with 28 printed gates within
{propext, Quot.sound}; channelSum_congr uses only propext. No new sorry,
axiom, Classical dependency, native_decide or noncomputable declaration.
Independent Sol and Luna read-only reviews confirmed original depth/source,
the full-heat versus bare distinction, projected insertion, signed/zero
cases and parameter scope. Only main compiled, serially with one worker,
20 GiB ceiling, 12 GiB OS reserve and automatic safety telemetry. The latest
preflight found no competing compiler/runner, 84 percent free memory and
zero swap. No safety or heartbeat limit was raised; local irreducibility
prevented needless unfolding. Initial elaboration/syntax errors were repaired
before the accepted checks. The generic factorization's accepted check
preceded the resumed physical consumers; its final source is unchanged.

Root imports are registration only; no aggregate/root/tree build, broad
audit or guard was run. CI remains manual-only. The safe-build skill confined
verification to the exact changed targets; no unchanged chart was printed.

Accepted logs and SHA-256 values:

- `/tmp/ym-passive-channel-factorization-repaired-20261001.log`:
  `cbcc091f2b791cfc345b13f567e3d2e38209ded549983f3512f8e1d899619624`.
- `/tmp/ym-family-channel-variance-final-20261001.log`:
  `cb42129c98879cdcebd41b352d001eeba2b3f3f0e1b2577109e8495b3deaefa3`.
- `/tmp/ym-family-channel-taylor-variance-accepted-20261001.log`:
  `aa559260c13cbefc4384ffaa8beca4be6a518c6e32e6fdd5d02501baa7fa79e5`.

## Addendum: retained channel square and band-only calibration fence

Two finite results sharpen and limit the preceding consumer. They preserve
the original action, source and same-object variance and do not close the
physical scaling input or any canonical chart node.

### Actual signed channel correction

All declarations below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean`.
For the SAME b_z and rho_z above, `familyChannelCurvature` at `:133`,
`familyChannelObservableSquare` at `:145`, and `familyChannelErrorBudget`
at `:155` compute

    Curv_ch = sum_z rho_z H[b_z^2*C_full Gamma_full(f,f)],
    Sq_ch   = sum_z rho_z H[(b_z*f)^2],
    Err_ch  = sum_z rho_z sourceErrorBudget(N-1,w,K,b_z,f).

`familyChannelObservableSquare_nonnegative` at `:165` proves Sq_ch>=0
using actual supported Haar squares and nonnegative original channel
weights. Individual b_z may be signed. The square retains the unshifted
complete f and is NOT identified with interacting centered variance.

`familyChannelTaylorDebt_le_retained` at `:288` proves, t=(1-w)^2/2,

    D_ch <= t*(A_ch-Curv_ch-48*Sq_ch)+Err_ch.

Its inputs are produced, not new analytic fields: each actual b_z is
supported; `spatialSpan_casimir` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCasimir.lean:294` supplies
the whole signed-family Cf=12f pin; the existing
`sourceSecondMoment_le_retainedSquare` in
`lean/YMGap/Continuum/SU2QuaternionSecondOrderRetainedSquare.lean:240`
accepts signed supported sources without a positivity premise. The exact
`sourceRemainder_secondOrder` and `sourceError_bound` in
`lean/YMGap/Continuum/SU2QuaternionCyclicSecondOrder.lean:197` and `:275`
retain actual cubic and omitted finite-cutoff terms. Multiplication by
rho_z>=0 and ordered finite summation preserve the inequalities; linear
regrouping keeps curvature signed and retains all off-diagonal face terms.

`padded_family_energy_le_retainedChannelVariance` at `:357` meets the
existing actual first-order producer and exact original-energy identity:

    E_original <= (h+t)*C*(Z*Var_original)
                  + t*(-Curv_ch-48*Sq_ch)+Err_ch, h=1-w.

This consumer uses positive depth n+1, original odd partition and mean,
strict spatial padding, 0<w<1 and K>=headCutoff(w). Arbitrary coefficients
and repeated faces remain. The debt estimate itself holds at every supplied
depth and finite K without asserting positivity of the truncated full heat.
Neither a favorable sign for Curv_ch nor a SAME-variance or scaling-small
estimate for Err_ch is proved.

### The chosen leading coefficient cannot supply survival smallness

`headFloor_le_stepEighth`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelCoefficientFence.lean:47`,
uses the existing `EulerProductStrictFloor.floor_le_euler` at N=1
(`lean/YMGap/Continuum/EulerProductStrictFloor.lean:64`). The actual Euler
floor is <=euler(w,1)=h, the retained head equals EulerFloor^2/8, and
0<h<1. Thus headFloor<=h^2/8<=h/8. For nonempty family size m, the local
floor l=headFloor^(28m) has l^2<=headFloor, and the local cap u is >=1.
Cleared positive-scalar cancellation then gives the exact conclusion

    h*C >= 96,  C=12*u^2/l^2.

`channelLeadingCoefficient_ge_ninetySix` at `:81` proves this for EVERY
0<w<1 and positive family-list size. No family coefficient, width, cutoff
or depth is used. Empty lists are deliberately excluded. The consumer
`relative_derivative_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:116`,
requires positive retainedFraction(c)=1-2c (same module `:51`), hence c<1/2. Therefore this
particular band-derived first-order ceiling with nonnegative debt payment
cannot provide that smallness. This is ONLY an obstruction to using the
chosen upper-bound coefficient that way, NOT a lower bound on actual
energy, channel cost, correlations, spectral gap or physical mass.

The next analytic producer must improve the actual source/variance comparison
without those band extremes, or retain and estimate the complete signed
correction jointly on a justified physical scaling family. Reducing positive
cutoff/cubic payment alone does not repair this leading coefficient. The
checked width-independent first-order estimate remains true and available;
no physical construction or canonical field is weakened or replaced.

### Verification and review

Both final focused checks exited zero, with all eight printed gates in
{propext, Quot.sound}. No new sorry, axiom, Classical dependency,
native_decide or noncomputable declaration. Sol implemented the bounded
channel producer without compiling; main repaired namespace/tuple/syntax
seams and supplied the original variance consumer. Luna independently
reviewed signs, whole-family scope and original depth/mean/partition. Main
implemented the coefficient fence; Sol and Luna reviewed its arithmetic
and bound-on-bound scope. Only main compiled under the SAME serialized
one-worker, 20 GiB ceiling, 12 GiB reserve and dynamic safety telemetry.
No heartbeat or safety limits were raised. Root imports were registered
but no aggregate/root/tree build, broad audit or guard was run. CI remains
manual-only; canonical chart unchanged and not reprinted.

Accepted logs and SHA-256 values:

- `/tmp/ym-channel-leading-coefficient-fence-accepted-20261001.log`:
  `fa3d8e90d74197edd4b9a228359cf5e8deb85c5a6725f54d50f7bec598b3559c`.
- `/tmp/ym-family-channel-retained-square-variance-final-20261001.log`:
  `f6fa085672209043ed9a0d0ace660157aa9cf1bdf4bf947451800260cbb293df`.

## Addendum: completed whole-family bond floor and every integer lag

After `65692f3`, the finite whole-family band now has a constructed SAME
completed physical consumer. No new analytic input is assumed. The family
is literal `familyState` with arbitrary rational signed coefficients; the
source, finite center, action and positive odd partition are unchanged.

### Finite and completed fraction

The declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondFloor.lean`.
`finite_family_energy_pin` at :147 uses the two existing squared-increment
pins on ONE insertion and cancels the rational factor two.
`finite_family_variance_pin` at :155 uses `source_family_shift` at zero,
then `middleRatio_congr` on both the source and its square, retaining the
actual moving center. All signed cross terms and unit terms survive.

With base<width and every face in spatialFaces(base),
`finite_family_energy_band` at :165 normalizes the existing band by ONLY
SAME positive oddMass. At stage k>=1 and terminal depth n+1 it gives

    E(k,n+1) <= (1-rho)*Var(k,n+1).

`finite_family_bond_fraction` at :181 uses the original exact finite
Var=Energy+Bond and additive rational cancellation to obtain

    rho*Var(k,n+1) <= Bond(k,n+1).

This cancellation assumes no sign of 1-rho or the variance and never
inverts a source or its variance. At diagonal stage s>=1, n=s-1 gives
the required positive depth and retained-mode guards.

`completed_family_bond_fraction` at :188 uses the existing Type-valued
variance/transfer Cauchy witnesses and the one-sided rational-limit order
theorem. Their original completed pins prove

    rho*B_V(v,v) <= connected_bond(0,ofSource(x),ofSource(x)),
    v = original centeredVector(x).

The ambient centered norm on the left is NOT the bond norm on the right.
`family_bond_floor` at :217 combines the existing distinct-face ambient
floor with positive scalar monotonicity. `family_bond_ne_zero` at :228
then excludes zero physical response when sum(c^2)>0. No quotient
representative is selected.

### Original correlator at every integer lag

The declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean`.
`connected_source_time_pairing` at :63 proves, for EVERY original intrinsic
source x, including multitime sources,

    connected_bond(k,ofSource(x),ofSource(x)) = B_V(v,T_(k+1)v).

The original odd reflected joint pin, literal advance composition, both
unit-stationarity laws and centered-vector pairing establish the exact
one-step offset. No new mean, transfer, carrier or time is substituted.

`family_rayleigh_floor` at :104 constructs the actual family input to
`BF4WilsonAllNomeResponseLower.response_geometric_lower`. The latter uses
positivity of powers of the SAME original time map.
`family_time_geometric_floor` at :110 and
`family_bond_geometric_floor` at :118 consequently give

    rho^(k+1)*varianceFloor(w)*sum(c^2)
        <= connected_bond(k,ofSource(x),ofSource(x))

at EVERY integer lag k. `family_bond_response_ne_zero` at :131 proves
strict nonzero for distinct interior faces and sum(c^2)>0, including lag
zero. It never decides equality of a constructive real or divides by a norm.

### Consumer, parameter budget and open residue

rho is the existing explicit familyResponseFraction(w,|qs|), with 0<w<1;
varianceFloor depends on w. Neither coefficient contains width, heat cutoff
or terminal depth. Nodup is needed only for the absolute coefficient floor,
not for the finite/completed variance fraction. Empty and repeated families
remain covered by that fraction; the strict nonzero guard excludes the
zero coefficient budget.

This supplies fixed-nome physical nontriviality and lower-response orbit
control for the COMPLETE signed family, extending the previous one-face
orbit. It does not identify different widths, supply changing-coupling
moduli, or keep rho^(k+1) away from zero at fixed physical time as spacing
vanishes. The lower coefficient can deteriorate with nome or family size.
It is NOT an improved upper decay/gap estimate. The useful complete signed
energy/SAME-variance scaling estimate, continuum survival, physical time/mass,
canonical continuum OS/QFT and every compact simple group remain OPEN.
No canonical field or displayed chart marker changes; no ASCII reprint.

### Focused verification and independent review

Both final focused file checks exited zero; all SEVEN floor and FIVE orbit
printed gates depend exactly on {propext, Quot.sound}. No sorry, new axiom,
Classical dependency, native_decide or noncomputable declaration is present.
The first floor drafts had a namespace omission and a whnf timeout; the
correct defining namespace and opaque original finite objects resolved
them without changing hypotheses, heartbeat or safety limits. Earlier
failed logs, including their generated sorryAx cascades, are not accepted
proof evidence. The orbit check passed on its first draft.

Independent Sol review checked signed source transport, original partitions,
zero cases, the scalar cancellation, regulator guards, exact time offset,
and the actual all-lag consumer. Luna independently matched all twelve
source gates to the accepted logs and checked fixed-nome scope/forbidden
shortcuts. Neither reviewer ran a compiler.

Main alone compiled, serialized with the safe-build skill and monitored
launcher: one worker, 20 GiB ceiling, 12 GiB OS reserve and dynamic telemetry.
Preflight found no competing Lean/Lake/test/runner process, 84 percent
pressure-free capacity and zero swap. No limit was raised. No full root/tree
build, broad audit or guard ran. Root imports are registered, not checked
in aggregate; the broad audit baseline was not regenerated. CI stays
manual-only.

Accepted logs and SHA-256:

- `/tmp/ym-family-bond-floor-final-20261001.log`:
  `b5eaaa4e054ebeed111198be736afbaeddbb3a97dc2440a157c0997741f9d2ab`.
- `/tmp/ym-family-bond-orbit-final-20261001.log`:
  `d001cde03bdb2051e5bcc2060e1e23f9d90efc3d8596d6fd530a4060bf88fdf1`.

## Addendum: quantified passive vacuum gain and SAME-variance Ward budget

After `df3824d`, coefficient-one angular contraction is sharpened by a
computed SU(2) nonvacuum attenuation. This is a NEW finite estimate and
actual-source consumer, not a new scaling assumption or continuum claim.

### Literal channels and vacuum

`SU2QuaternionProductHeatChannelNomeComparison.product_channel_sum_pin`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatChannelNomeComparison.lean:203`)
matches computed charge/weight/polynomial tags to every original finite
real/imaginary Gram channel, including inverse basis normalizers. Charges
add under Cartesian multiplication and are zero or at least three.
`productChannels_nome_interpolation` (same file :340) consequently proves

    S_w(F) <= (1-w^3)*S_0(F) + w^3*S_1(F), 0<=w<=1.

Every K, including zero, and repeated selected blocks are allowed. F is
nonnegative on supported polynomials; no out-of-carrier positivity is
assumed. The SAME F/source is frozen in all three auxiliary weight tests.
This is not comparison of physical Yang--Mills laws at different couplings.

`SU2QuaternionProductHeatChannelVacuum.heatChannels_zero_nome`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatChannelVacuum.lean:109`)
retains exactly the degree-zero real unit/imaginary zero leaves;
`productChannels_zero_nome` (same file :166) gives S_0(F)=F(polyOne), and
`productChannels_vacuum_contraction` (same file :186) supplies its consumer.

`SU2QuaternionPassiveChannelStrictAngular.channel_angular_zero_nome`
(`lean/YMGap/Continuum/SU2QuaternionPassiveChannelStrictAngular.lean:90`)
identifies this vacuum with the literal conditional projection P_ids(q).
`channel_angular_vacuum_le_raw` (:106), `channel_angular_vacuum_bound`
(:119) and `channel_angular_gain_lower` (:145) prove

    A0 <= Araw,
    A_ch <= (1-w^3)*A0+w^3*Araw,
    (1-w^3)*(Araw-A0) <= Araw-A_ch.

Here Araw=weightedAngularEnergy(q,f), A0=weightedAngularEnergy(P_ids q,f),
and A_ch is the actual complete finite angular channel sum. Supported q,f,
valid distinct ids and passive independence of f are retained. At nome one
the Bessel step is an INEQUALITY, not assumed finite-cutoff completeness.

### Actual source, complete signed energy and Ward join

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelVacuumGain.lean`.
`familyRawAngularCost` (:78) and `familyVacuumAngularCost` (:86) compute
these costs on q=projectedEndpointSource(w,K,width,terminalMessage(depth))
and f=spatialSpan(width,c,qs), with the original spectator schedule.
`family_vacuum_cost_le_raw` (:95), `family_first_order_vacuum_bound`
(:112) and `family_angular_gain_lower` (:133) supply their actual instances
for every width/depth/cutoff, without a channel-count coefficient.

`padded_family_energy_vacuum_bound` (:155) preserves the original exact
Taylor debt D_ch and gives E<=h*((1-w^3)*A0+w^3*Araw)+D_ch, h=1-w.
`padded_family_normalized_energy_vacuum_bound` (:170) divides ONLY by the
SAME proved-positive oddMass. Interior padding is required for these
energy consumers; strict nome and headCutoff guard enter normalization.

`padded_family_energy_ward_gain` (:212) joins the actual raw first-order
pin to `BF4ExactSlabFixedSpatialFamilyJointCorrection.family_firstOrder_defect_ward`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointCorrection.lean:77`).
At depth n+1, write delta=angularWeightDefect, R=wardResidual, Z=oddMass,
and Var=the SAME original moving-center oddVariance. Araw+delta+R=12*Z*Var
then gives the stronger signed ceiling

    E <= 12*h*(Z*Var)+D_ch
         -h*(delta+R+(1-w^3)*(Araw-A0)).

The two signed remainder terms, omitted finite-cutoff modes, original mean,
partition, action and coupling stay unchanged. No sign is assumed for
D_ch, delta or R; repeated/empty families and zero coefficients are allowed.
The subtracted new gain is nonnegative, but is NOT a variance-relative floor.
Algebraically h*(1-w^3)=h^2*(1+w+w^2). This second-order gain alone cannot
alter the leading 12*h coefficient. No changing-source remainder bound follows.

### Exact next input and SAME-carrier consumer

For a chosen relative one-step loss delta_j, the remaining finite producer
is an upper bound on the COMPLETE signed bracket

    J_j = D_ch,j - h_j*(W_j+R_j+(1-w_j^3)*(Araw_j-A0_j))
    J_j <= (delta_j-12*h_j)*Z_j*Var_j.

Here W_j is angularWeightDefect, distinct from the chosen relative loss
delta_j. This must hold on the original regulator rectangle
for an explicitly justified changing-coupling/spatial/spacing family.
`BF4WilsonAllNomePlaquetteFamilyBondFloor.finite_family_energy_pin` and
`finite_family_variance_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondFloor.lean:147`, :155)
identify its actual finite family quantities with the constructed limit
sequences. `BF4WilsonAllNomeTemporalEnergyLimit.energyLimit_completed_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218`) and
`BF4WilsonAllNomeMarginalVarianceLimit.varianceLimit_completed_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:236`)
are the SAME all-nome completed loss and ambient-norm pins.
The downstream response theorem is
`BF4WilsonAllNomeResponseLower.response_geometric_lower`
(`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:117`), and
`BF4WilsonAllNomePlaquetteFamilyBondOrbit.connected_source_time_pairing`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:63`)
supplies its physical bond time-offset pin. These are existing declarations,
not a newly proved relative-loss instance in this milestone. The legacy
JointCompletion survival theorem is not substituted for this carrier.

`BF4ExactSlabFixedSpatialCenteredTransferReserve.centered_transfer_angular_reserve`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredTransferReserve.lean:110`)
gives an upper bound on a DIFFERENT output reserve, not the required upper
bound on J_j. No constructed physical scaling family or useful complete
signed-bracket estimate is supplied here. Physical-time survival also needs
its loss rate controlled against spacing and nonvanishing normalized states.
Continuum survival, physical mass, canonical OS/QFT and all groups remain
OPEN. No canonical field, chart marker or ASCII layout changes.

### Focused verification and review

Four final focused checks passed 2+3+5+6=16 gates, all exactly
{propext, Quot.sound}. The five-gate angular source supersedes its earlier
four-gate log; the six-gate BF4 log below supersedes the earlier four-gate
draft. The accepted six-gate check passed on its first check; the word
"first" in its filename does not imply a failure or incomplete source.
No sorry, new axiom, Classical, native_decide or noncomputable declaration
is present. Independent Sol mathematical/source review and Luna final
source/log gate review passed; reviewers did not run compilers.

Main alone compiled, serialized through the monitored safe-build launcher,
one worker, 20 GiB ceiling, 12 GiB reserve and dynamic telemetry. Fresh
preflight found no competing compiler/test/runner, 84 percent pressure-free
capacity and zero swap; no limit was raised. No full root/tree build, broad
audit or guard ran; root imports are registered but not aggregate-checked.
CI remains manual-only. The intervening status-only user response was not
proof progress; this continuation completed the quantified-gain milestone.

Accepted log SHA-256:

- `/tmp/ym-channel-nome-comparison-final-20261001.log`:
  `b241d446bc3c7bfe0e9a011ab9df0a7714ecd47a6fc7439c92a66bde8784d732`.
- `/tmp/ym-channel-vacuum-final-20261001.log`:
  `3050ef2bdc2cf0b8c9ca32f4a5f2e4fce9ac3b2717438b46313262d9531b4c04`.
- `/tmp/ym-passive-strict-angular-complete-final-20261001.log`:
  `8a542decac6530c2e15428e07b8b1ed0f5e5e1d16c54424d77e6966db656dea7`.
- `/tmp/ym-family-channel-ward-gain-first-20261001.log`:
  `dcf49183113a1785403a26dac01bea87edbac4bcb427e8490e9e2f90213f4953`.
