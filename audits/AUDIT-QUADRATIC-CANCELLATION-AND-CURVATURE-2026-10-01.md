# Quadratic cancellation and original observable curvature

Date: 2026-10-01 UTC. A short local argument now preserves the second-order
mixed-minus-diagonal cancellation before absolute estimates. It separates
two proved nonpositive contributions from one signed observable-curvature
insertion, and has a concrete consumer under the original signed family's
SAME interacting variance. It does not supply a scaling-uniform estimate.

## Literal derivatives and constructed square data

The operator is the existing positive Casimir C=-sum X^2, not the physical
continuum Hamiltonian. `activeCasimirPolynomial` is defined in
`lean/YMGap/Continuum/SU2QuaternionChannelCasimirSquare.lean:50`.
`SU2QuaternionActiveCasimirProduct.activeGamma`
(`lean/YMGap/Continuum/SU2QuaternionActiveCasimirProduct.lean:42`)
is the polynomial sum of (Xp)*(Xq) over the same original blocks and all
six angular planes per block. `activeCasimirPolynomial_mul`, line 214,
proves C(p*q)=(Cp)*q+p*(Cq)-2*Gamma(p,q) at coefficient equality.
`activeGamma_mul_right`, line 307, proves its actual product rule.

`activeGamma_squareCertificate`, line 422, returns Type-level supported
square data for Gamma(p,p). Its auxiliary structurally recurses over the
block list, with explicit six-square addition at each block. The product
of the diagonal certificates uses the existing `Certificate.mul`, preserving
overlapping variables and all cross terms. No choice or positivity premise
is substituted for those witnesses.

## Exact local cancellation

All declarations here are in
`lean/YMGap/Continuum/SU2QuaternionSecondOrderCancellation.lean`.
Write B=q*Cf-2*Gamma(q,f), G=Gamma(f,f). The product rule gives

    C(q*f)   = f*Cq + B
    C(q*f^2) = f^2*Cq + 2*f*B - 2*q*G.

`quadratic_polynomial_cancellation`, line 61, therefore proves, before Haar
integration or any estimate,

    (Cq)*C(q*f^2) - (C(q*f))^2 = -2*q*(Cq)*G - B^2.

`sourceSecondMoment_cancellation`, line 118, pins this to the EXISTING
full finite-tree coefficient D2 through `sourceSecondMoment_literal`.
It applies to every supported signed source and observable, not facewise
pieces with discarded off-diagonal terms.

`casimir_pair_gamma`, line 153, identifies the literal Haar Casimir pairing
with the polynomial Gamma using existing original-block integration by
parts. `curvatureFlux_ibp`, line 161, and `gradientFlux_ibp`, line 181,
prove H[q*(Cq)*G]=H[Gamma(q,q)*G]+H[q*Gamma(q,G)] and
H[q^2*CG]=2*H[q*Gamma(q,G)]. Consequently
`sourceSecondMoment_curvature`, line 216, proves the exact split

    D2 = -H[B^2] - 2*H[Gamma(q,q)*Gamma(f,f)] - H[q^2*C Gamma(f,f)].

`sourceSecondMoment_le_curvature`, line 272, removes only the first two
nonpositive contributions, using explicit supported square certificates,
and yields D2<=-H[q^2*C Gamma(f,f)]. The exact split remains available;
this upper bound can be weaker when the negative contributions matter.
The last insertion is signed. Neither q>0 nor an eigenpin for f gives
it a useful sign in any theorem of this checkpoint.

`sourceEnergy_le_curvature`, line 312, retains the original finite-cutoff
energy and cubic/omitted-mode payments from the previous second-order
checkpoint. No untruncated heat operator is substituted.

## Concrete original family and variance consumer

`BF4ExactSlabFixedSpatialFamilyCurvature.curvatureMoment`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCurvature.lean:69`)
uses q=projectedEndpointSource(w,K,width,terminalMessage(w,K,width,n)).
Both C and Gamma act on the full List.range of N=length(baseLinks width).
The original support producers and N-1+1=N are supplied explicitly.
There is no unprojected depth n+1 source or alternate law.

`quadraticCoefficient_le_curvature`, line 77, replaces D2 by the proved
upper bound while leaving sourceFirstOrder intact. `curvatureVarianceCeiling`,
line 95, retains the actual cubic/cutoff budget, -h*angularWeightDefect and
-h*completeWardResidual under original oddMass, h=1-w.
`padded_family_energy_le_curvature`, line 136, proves

    E_original/Z_original <= 12*h*Var_original + curvatureVarianceCeiling.

The consumer uses the EXISTING family energy/variance identity, with the
original mean, arbitrary signed coefficients and repeated faces. No source
or variance inverse and no stationarity premise is introduced.

## Remaining analytic frontier

Useful control of this combined correction relative to SAME variance on
a justified physical scaling family remains open. In particular the
observable-curvature insertion, complete Ward residual and angular weight
defect are not bounded with a useful relative rate. The actual finite-tree
cubic/cutoff budgets still need changing-source control. A rearrangement
of this signed correction is not a proof of its smallness.

Physical spatial/spacing-uniform decay, nonzero continuum survival, the
full same-theory continuum OS/QFT construction, physical time/Hamiltonian
mass calibration and every compact simple group remain open. This is a
kinematic finite SU(2) identity, not a new non-abelian continuum estimate.
No canonical frontier field or displayed chart marker changes.

## Verification boundary

Three final focused checks exited zero with 25 printed gates within
{propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide or noncomputable declaration. Sol derived and implemented
the product rule; independent Sol and Luna source reviews checked the
signs, square data, original source depth, cutoff and variance pins.
Namespace, scalar-reflection, notation and structural-recursion errors
were repaired before acceptance, without changed mathematical inputs.

Only main compiled, serially using the safe launcher with one worker,
20 GiB ceiling, 12 GiB OS reserve and continuous dynamic telemetry.
Preflight found no competing Lean/Lake/test/runner process, 82 percent
memory free and zero swap. No safety limit was raised. Root imports were
registered but not checked in aggregate. No full root/tree build, audit
or guard ran; CI remains manual-only. The documentation skill preserved
the distinction between finite cancellation and its missing scaling input.
No unchanged ASCII chart was reprinted.

Final logs under `/tmp/`, with SHA-256:

- `ym-active-casimir-product-accepted-20261001.log`:
  `d9048ae194f42393b47ada90e1ec190e788b8648209bc0f20a92fe43ecb46836`.
- `ym-second-order-cancellation-repaired-20261001.log`:
  `cfa760fee09b1696c33e250c6d710052d41c6758f60fa994b94f685f32a10c33`.
- `ym-family-curvature-accepted-20261001.log`:
  `6b7c25188cd35ca88c0e4d10704cdb70bf7a616c5208b6613efb7a6b343f78d1`.
