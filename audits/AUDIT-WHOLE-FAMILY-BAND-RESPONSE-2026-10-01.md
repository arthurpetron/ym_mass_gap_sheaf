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
