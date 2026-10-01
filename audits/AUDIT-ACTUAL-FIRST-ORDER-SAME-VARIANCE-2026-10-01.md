# Actual terminal first order and joint signed variance control

Date: 2026-10-01 UTC. The actual positive-depth projected terminal source now
has a first-order angular-energy bound against the SAME original centered
interacting variance. Its coefficient is independent of late cutoff and
terminal depth at fixed nome and full width. The original energy consumer
combines both signed first-order corrections before estimating them, leaving
curvature and Taylor debt explicit. This is not a physical scaling estimate.

## Original objects and constructed comparison

Write d=n+1, f=spatialSpan(width,c,qs), q=projectedEndpointSource(w,K,width,T_d),
W=V*T_d*T_(d+1), Z=oddMass(w,K,width,d), and Var=oddVariance(f) at that SAME
depth and original mean. Coefficients c are arbitrary rational numbers;
faces may repeat. For the source comparison each face belongs to the full
spatial slice. The energy consumer additionally requires strict padding and
faces from the smaller slice, which supply the actual fringe independence.

Let m=H[V*T_n]>0, v_-=spatialFloor(w,width), v_+=spatialCeiling(w,width),
k_-=kineticFloor(w,width), and k_+=kineticCap(w,width). Define
L0=v_-^2*k_-^3 and U0=v_+^2*k_+^2. Existing transfer floors/caps and the
actual fringe projection construct certificates for

    q <= v_+*k_+*m,     W >= L0*m^2.

These are positive-polynomial certificates under arbitrary Haar insertions,
not assumed pointwise inequalities or a replacement law. Evidence:
`BF4ExactSlabFixedSpatialTerminalSourceBounds.projectedSource_upperCertificate`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSourceBounds.lean:130`,
and `marginalWeight_lowerCertificate` in the same file at line 196.

The complete signed physical family has H[f]=0 and H[Gamma(f,f)]=12*H[f^2].
Its bare squared norm is no larger than H[(f-center)^2] for ANY rational
center, including the unchanged original W-mean. The declarations are
`family_haar_zero`, `family_gamma_square`, and `family_shifted_square_ge`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBareHaar.lean:124`,
`:149`, and `:172`. `family_sourceFirstOrder_gamma` at line 94 identifies
A=sourceFirstOrder with H[q^2*Gamma(f,f)], retaining all signed cross terms.

The resulting inequalities are A<=12*U0*m^2*H[f^2] and
L0*m^2*H[f^2]<=Z*Var. Scaled substitution, without dividing by m or Var,
gives L0*A<=12*U0*Z*Var. Evidence:
`BF4ExactSlabFixedSpatialFamilySourceVarianceBound.family_firstOrder_variance_cleared`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilySourceVarianceBound.lean:252`.
`marginal_centered_square` at line 150 pins the centered insertion to the
original Z*Var without an extra fringe restriction.

`firstOrderVarianceConstant` at line 281 computes U=12*U0/L0; its positivity
is proved at line 286. `family_firstOrder_variance_bound` at line 293 gives
A<=U*Z*Var. Only the explicit positive scalar L0 is inverted.

## Joint signed energy consumer

Put h=1-w, alpha=h^2/2, Delta=angularWeightDefect, and R=wardResidual.
The actual marginal Ward and source-weight identities give

    A + Delta + R = 12*Z*Var.
    alpha*A - h*Delta - h*R <= ((h+alpha)*U - 12*h)*Z*Var.

Both terms remain signed until this exact combination. Source, mean,
normalization and terminal depth are unchanged. Evidence:
`BF4ExactSlabFixedSpatialFamilyJointCorrection.family_firstOrder_defect_ward`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointCorrection.lean:77`,
and `jointRaw_le_variance` in the same file at line 149.

Let debt=alpha*(-curvatureMoment-48*projectedObservableSquare)+sourceErrorBudget.
`jointDebt` at line 132 retains the signed whole-family curvature, the actual
negative source square, and the original cubic and omitted-mode cutoff
budgets. `padded_family_energy_le_jointVariance` at line 293 proves

    normalizedEnergy <= (h+alpha)*U*Var + debt/Z.

The original leading 12*h*Var cancels algebraically against the corresponding
joint correction; no separate helpful sign is assigned to Delta or R.

## Parameter dependence and remaining frontier

All statements retain 0<w<1 and K>=headCutoff(w). The source and variance
are at positive depth n+1. U names only w and width, not K, n, coefficients
or family-list size. In terms of S=number of spatial faces and T=number of
temporal faces, its defining factors are

    U = 12*prefixCap(w)^(2*S+2*T) / headFloor(w)^(2*S+3*T).

This expansion is algebra from the defining factors, not a separate new
Lean power identity. See `spatialFloor` and `spatialCeiling` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCentralDensity.lean:72` and `:75`,
and `kineticFloor` and `kineticCap` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:57` and `:61`.
There is no width-uniform or coupling-uniform assertion, no beta/spacing
calibration, and no proved scaling-small coefficient or debt/variance bound.

The next required input remains useful control of the COMPLETE signed cost
against SAME variance on a justified physical family. The new first-order
producer removes a finite comparison gap; it does not supply that scaling
input. Physical decay across scales, nonzero continuum survival, mass
calibration, full same-theory QFT and every compact simple group remain OPEN.
No canonical frontier field or displayed chart marker changes.

## Verification

Four final focused file checks exited zero; all 35 printed gates stay within
{propext, Quot.sound}, with three axiom-free step definitions. No sorry, new
axiom, Classical dependency, native_decide or noncomputable declaration.
Independent Sol and Luna reviews checked the coefficients, original center,
depths, zero cases and signed consumer. Initial namespace, rational-setoid
chaining, reflection syntax and unfolding errors were repaired without
changing the mathematical hypotheses or raising heartbeat/memory limits.

Only main compiled, serially through the monitored launcher with one worker,
20 GiB ceiling and 12 GiB OS reserve. Preflight found no competing
Lean/Lake/test/runner process, 83 percent pressure-free capacity and zero
swap. Root imports were registered but not checked in aggregate. No full
root/tree build, audit or guard ran. CI remains manual-only. The documentation
skill kept finite parameter control separate from its open physical consumer;
the unchanged canonical ASCII chart was not reprinted.

Final logs under `/tmp/`, with SHA-256:

- `ym-terminal-source-bounds-final-20261001.log`:
  `1ad3bfb86edc486236e790d69ca57841c71cca817e0f4ea8665b2e7465730b8f`.
- `ym-family-bare-haar-final-20261001.log`:
  `0af9d2e65d7bb87cd6a9e1e5e9eea2544ee3cc6c84885008b15fd60f14758a98`.
- `ym-family-source-variance-final-20261001.log`:
  `ae9fb6efe9f5f502c34adfc62f83481879d4f0b47402319e46397f3500b1deb7`.
- `ym-family-joint-correction-accepted-20261001.log`:
  `740034386772b96df5342bfa25d967afb9b0bfc92cc7ac882147bc10a500a4a9`.

## Addendum: two-sided fixed-source heat-step and moment limits

The actual fixed-source zero-step calculations now have quantitative joins
to the ORIGINAL finite-cutoff energy and moments. These are constructed
moduli, not new assumed analytic fields. They do not control a changing
terminal source along a physical scaling trajectory.

### Original energy slope

The declarations below are in
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceSlope.lean`.
`sourceEnergy_ge_firstOrder_sub_quadratic` at line 36 supplies the lower
companion to the existing upper Taylor estimate, retaining BOTH signed
pair-remainder bounds. `slopeCap` at line 65 computes

    cap = 1 + abs(sourceTaylorBudget(tail,a,f)),
    radius = e / cap,  h = 1-w,
    h*(A-e) <= E_original <= h*(A+e).

`sourceEnergy_slope_interval` at line 98 proves the interval whenever
0<=w<1, h<=radius and K>=sufficientCutoff(w). Here A is exactly the
existing weightedAngularEnergy(tail,a,f), and E_original is the full
List.range(tail+1) original product-heat energy of the SAME supported
source and observable. `slopeRadius` at line 80 and `slopeCertificate`
at line 145 return the positive radius and the all-guarded-cutoff proof
as Type-level data. Neither h nor a variance is inverted in the inequality.

### Original signed moment endpoint

The declarations below are in
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceMomentLimit.lean`.
`zeroStepMoment` at line 31 is H[(a*p)*a], not a replacement positive-step
interacting variance. `momentCap` at line 35 computes

    cap = 1 + abs(pairCasimir(tail,a,a*p)) + abs(pairBudget(tail,a,a*p)).

`sourceMoment_endpoint_interval` at line 64 proves
M0-h*cap<=H[(a*p)*P(a)]<=M0+h*cap for 0<=w<1 and EVERY
K>=sufficientCutoff(w). The h^2<=h reduction explicitly uses w>=0.
`momentRadius` at line 44 and `momentCertificate` at line 124 return
e/cap and its two-sided e-precision bound. The insertion p may be signed;
only a has a supported-source premise. The actual cutoff and heat operator
are retained throughout.

### Consumer, scope and verification

These certificates allow a concrete FIXED-source Haar/Ward endpoint
calculation to be tested at genuine positive heat steps. The source is
fixed BEFORE w varies. Applying the theorem separately to parameter-dependent
terminal sources does not produce a common radius. The required useful
SAME-interacting-variance bound for the actual terminal/channel source on a
justified physical family remains OPEN, as do scaling survival, physical
mass, full continuum QFT and every compact simple group.

Both final focused checks exited zero, with 13 printed gates within
{propext, Quot.sound}. Independent read-only reviews checked the signs,
cutoff quantifiers, signed insertion and returned witness scope. No new
sorry, axiom, Classical dependency, native_decide or noncomputable
declaration. One unused-binder warning in slopeCertificate is harmless.
Only main compiled with the monitored one-worker 20 GiB ceiling and 12 GiB
OS reserve. The safe-build skill confined verification to the exact targets.
No aggregate/root/tree build, broad audit or guard ran; CI stays manual-only.
No canonical chart marker changed, so no chart was reprinted.

Accepted logs and SHA-256:

- `/tmp/ym-source-slope-first-20261001.log`:
  `4aa12a9f0e66c67c3080cf12d8bdfb893d1d3e1e2cd1e76791d8ae95f1237fa3`.
- `/tmp/ym-source-moment-limit-accepted-20261001.log`:
  `52532fc6f2ac2b3851856fd3e0616e57a91f581f401fc79e9aa7dc49dd2b7149`.

## Addendum: concentrated-source Ward obstruction on actual heat

This supplies the preceding fixed-source certificates' concrete consumer.
For each requested nonnegative coefficient C, actual source/nome witnesses
defeat E<=C*(1-w)*B, where E and B are ORIGINAL finite-step energy and
uncentered second moment. This is not an actual terminal-family claim.

### Exact one-link source and Ward identities

Declarations in
`lean/YMGap/Continuum/SU2QuaternionConcentratedSourceWard.lean`:

- `sourceCertificate`, line 87, constructs the NONNEGATIVITY certificate
  of q_N=(x1^2+x2^2+x3^2)^N. This is not pointwise strict positivity.
- `radial_carrier`, line 98, pins radial+chi_1^2/4=1 on the SAME unit
  quaternion Haar carrier under arbitrary insertions.
- `fundamental_casimir`, line 112, pins C f=3f under every original Haar
  insertion. It does not equate padded and unpadded raw monomial keys.
- `fundamental_sourceSquare_gamma`, line 192, proves the exact coefficient
  identity Gamma(f,q_N^2)=-4N*f*q_N^2.
- `sourceSquare_moment`, line 382, proves Z=(N+1)*J, with Z=H[q_N^2]
  and J=H[q_N^2*f^2]. `sourceSquare_angular`, line 390, proves A=(4N+3)*J.

Declarations in
`lean/YMGap/Continuum/SU2QuaternionConcentratedSourceMoments.lean`:
`radialMass_step`, line 243, proves (2k+4)*Z_(k+1)=(2k+3)*Z_k for
Z_k=H[radial^k]. `radialMass_pos`, line 251, inducts from Z_0=1.
`source_power_add`, line 277, identifies the actual source square with
the double radial power. `mass_pos`, line 288, and `secondMoment_pos`,
line 294, supply Z>0 and J>0 without assumed nondegeneracy.
`firstMoment_zero`, line 306, follows directly from Ward and positive
coefficient cancellation, without a parity or high-degree expansion.

### Computed original positive-step witnesses

All declarations below are in
`lean/YMGap/Continuum/SU2QuaternionConcentratedSourceHeatFence.lean`.
`escapeExponent`, line 47, returns N=C.num.toNat; its coefficient proof
at line 49 gives 2C<4N+2 for C>=0. `step`, line 77, computes

    h = min(1/2, slopeRadius(0,q_N,f,J), momentRadius(0,q_N,f^2,J)),
    w = 1-h,  0<w<1.

`zeroStep_square_pin`, line 66, identifies H[(q_N*f^2)*q_N] with J.
The slope error J gives E>=h*(4N+2)*J; the signed moment error J gives
B=H[(q_N*f^2)*P(q_N)]<=2J. Since h,J>0, their exact combination proves

    E > C*h*B

in `energy_gt_same_secondMoment`, line 120, for EVERY
K>=sufficientCutoff(w). `obstruction`, line 183, returns N,w and this
all-guarded-cutoff proof as Type-level data. No endpoint replaces a
positive-step heat expression; no interacting variance is inverted.

### Scope and next actual-source input

The finite-step B is UNCENTERED. The proved zero first moment belongs to
the bare Haar endpoint, not an asserted positive-step centering identity.
These q_N are nonnegative certified sources, not pointwise-strict sources
or identified BF4 terminal messages. Consequently this refutes only a
nonnegativity-only source-independent comparison. It refutes no actual
terminal-source theorem, scaling trajectory, continuum theory or mass gap.

The stronger existing actual-source input is
`BF4ExactSlabFixedSpatialEndpointRelativeBound.projectedEndpointRelativeBound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:96`.
Its original same-channel consumer is
`projectedEndpoint_familyChannelDerivative_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelRegularity.lean:61`,
and `padded_plaquetteChannel_firstMoment_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelFirstMoment.lean:136`.
Their cap-squared cost is still not useful scaling control. The original
positive-depth heat-recursion pin is `terminal_cons_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.lean:53`.
An improved integrated heat-score estimate from that recursion is a next
candidate to investigate, not a proved estimate or an assumed new field.
Read-only search found no existing one-sided heat-relative Casimir bound
with useful O(1/(1-w)) cost. The alternative candidate is the integrated
spectral inequality (1-w)*lambda*w^(2*lambda)<=w^lambda and its actual
source-pairing/derivative join. The relevant original grouping declaration
is `polynomial_grouped_heat_pairing` in
`lean/YMGap/Continuum/SU2QuaternionGroupedHeatComparison.lean`; source
grouping alone does not justify arbitrary spectator-weight orthogonality.
This candidate has not been formalized in this checkpoint and supplies
no new terminal or scaling estimate.
The actual complete signed SAME-variance scaling bound, survival, physical
mass, full QFT and every-group construction remain OPEN.

### Focused verification

Three final focused target checks exited zero with 30 printed gates within
{propext, Quot.sound}; the exponent definition is axiom-free. Independent
Sol/Luna reviews passed on the Ward signs, strict-moment producer, original
finite-step joins, all-cutoff quantifier and nonnegative/uncentered scope.
Initial namespace, scalar-parenthesis and rational simplification errors
were repaired. A false raw-key Casimir statement was replaced by its actual
arbitrary-insertion Haar equality; no canonical field was weakened.
There is no new sorry, axiom, Classical, native_decide or noncomputable
declaration in the accepted sources.

Main alone compiled, serially under the monitored one-worker 20 GiB cap
and 12 GiB OS reserve. Preflight found 84 percent pressure-free memory,
zero swap and no competing compiler/test/runner. No limit was raised.
The safe-build skill confined verification to these targets. No full
root/tree build, broad audit or guard ran. CI remains manual-only; the
unchanged canonical chart was not reprinted.

Accepted logs and SHA-256:

- `/tmp/ym-concentrated-source-ward-accepted-20261001.log`:
  `b22411972470d0523786b746e39421f0de0145cfb0a3c326f31aa31fef4d9485`.
- `/tmp/ym-concentrated-source-moments-accepted-final-20261001.log`:
  `1f23bf2af13a48af52088d6e650cd767d8b1ad6bd7a77c55fcf8dbc7d4e16324`.
- `/tmp/ym-concentrated-source-heat-fence-accepted-20261001.log`:
  `9e755e1ad176d98c6b6359037831fd1b66ab11c23a8701c82794ee9b63752b07`.

## Addendum: original one-head output angular smoothing

Date: 2026-10-01 UTC. The integrated candidate above now has a proved
scalar-to-concrete-local-operator join. This supplies an output-side estimate
on an actual heat-smoothed source; it is not a new assumed terminal certificate.

### Scalar input and exact output realization

`SU2HeatSquaredCasimirSmoothing.casimir_power_le_one`,
`lean/YMGap/Continuum/SU2HeatSquaredCasimirSmoothing.lean:24`, proves
h*lambda*w^lambda<=1, h=1-w, using the exact finite geometric sum.
`qpow_squared_casimir_smoothing`, `:57`, pays a squared heat multiplier.
`attenuation_squared_casimir_smoothing`, `:75`, applies this to the
ORIGINAL finite-cutoff attenuation a_d, with lambda=d*(d+2):

    h*lambda*a_d^2 <= a_d.

The quantifiers are 0<=w<=1 and every K,d; omitted degrees have a_d=0.
No input-degree-below-cutoff, sufficient-cutoff or pointwise heat-floor
premise is used.

`SU2QuaternionGroupedAngularEnergy.carrier_harmonic_sum_angular_energy`,
`lean/YMGap/Continuum/SU2QuaternionGroupedAngularEnergy.lean:262`, generalizes
the existing angular Pythagoras to a carrier represented by any finite
distinct-degree harmonic sum. It reuses the proved carrier derivative
congruence and original angular orthogonality, not a supplied norm identity.

`SU2QuaternionHeadHeatSmoothing.headMap_grouped`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatSmoothing.lean:64`, pins the ACTUAL
computed headMap under EVERY arbitrary Haar insertion. The head map is the
existing conditional original two-link heat with all spectators shared.
`headMap_angular_grouped`, `:138`, consequently proves

    H[angularSquare(P_head p)] = sum_d lambda*a_d^2*H[group_d^2].

The groups are computed from the supported ORIGINAL p. Complete signed
equal-degree contributions are added before squaring, so their cross terms
remain. The actual output energy is not replaced by an abstract norm budget.

### Concrete consumer and residue

`headMap_angular_smoothing`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatSmoothing.lean:174`, proves

    (1-w)*H[angularSquare(P_head p)] <= H[p*P_head p]

for every supported signed p, every cutoff, every spectator count and
0<=w<=1. Each nonnegative full grouped square multiplies the scalar bound;
`HeadHeatDiagonal.polynomial_diagonal` supplies the SAME original RHS.
The numerator constant is one; all coupling dependence is explicit in h.
This is a source-independent rescaled one-head smoothing estimate. For
w<1 its unscaled cost is 1/(1-w), not a heat-floor quotient. At w=1 the
statement is degenerate, not a uniform unscaled derivative bound.

The RHS is UNCENTERED Haar heat pairing. It is not the original interacting
variance or an OS form. The headMap preserves spectator coordinates,
whereas `productMap` integrates omitted coordinates; they are not identified.
The actual terminal recursion includes the spatial action and full product
heat. Its existing signed degree-path expansion does not prove joint-mode
orthogonality or permit dropping spectator/endpoint weights.

NEXT remains their genuine weighted composition and SAME-variance join,
with joint signed corrections retained along a justified physical family.
A centered original heat-pairing refinement would also need actual constant
and linearity pins; merely applying the inequality to a shifted polynomial
does not assert that refinement. No new analytic input field is introduced.
Actual signed physical scaling, nonzero continuum survival, physical mass,
full QFT and every compact simple group remain OPEN. No canonical marker
changed; no unchanged ASCII chart was printed.

### Focused verification

Three final focused file checks exited zero with eight printed gates, seven
new and one existing. All dependencies are within {propext, Quot.sound};
no new sorry, axiom, Classical dependency, native_decide or noncomputable
declaration occurs. Independent Luna review passed the cutoff cases,
degree grouping, signed source, shared spectators and inequality direction.
Sol's source review confirmed that no immediate terminal/variance join is
available. Missing namespaces and an unspecified scalar multiplier were
repaired before acceptance, without changing the mathematical estimate.

Main alone compiled through the safe-build skill's focused monitored
launcher, one worker, mandatory 20 GiB ceiling and 12 GiB OS reserve.
Preflight found 84 percent pressure-free memory, zero swap and no competing
Lean/Lake/test/runner process. No limit was raised. Root imports register
the modules only; no aggregate/root/tree build, broad audit or guard ran.
CI remains manual-only. Accepted logs and SHA-256:

- `/tmp/ym-squared-casimir-smoothing-accepted-20261001.log`:
  `76afd52791fedb3119e3aeb3c121269915d278ec30787454b21c861239219681`.
- `/tmp/ym-harmonic-output-angular-20261001.log`:
  `77c7512f5143802448f8182dd79a621befd9936dd5fbb9f36a11ec0449f55232`.
- `/tmp/ym-original-head-smoothing-final-scope-20261001.log`:
  `ccfd7e4254a377a96b2c4ff6ca52ec0e3f2facf4070fc1e672c1df0cf4bc63f0`.

## Addendum: full-product and original terminal output smoothing

Date: 2026-10-01 UTC. The earlier local smoothing estimate now has a
proved full-product and ORIGINAL interacting-transfer output consumer.
No endpoint-observable/interacting-variance comparison is asserted.

### Literal paths, eigenvalues and scalar budget

`product_squared_casimir_smoothing`,
`lean/YMGap/Continuum/SU2HeatProductCasimirSmoothing.lean:41`, proves

    (h*totalCasimir(ds))*productAttenuation(ds)^2 <= productAttenuation(ds),
    h=1-w.

Every retained path has exactly w raised to its TOTAL integer Casimir;
an omitted coordinate makes the actual attenuation zero. Applying the
existing one-power bound to the total, rather than summing separate
one-link estimates, introduces no extent factor. Every cutoff and
0<=w<=1 are included. At w=1 the rescaled derivative bound is degenerate;
this is not an unscaled coupling-uniform regularity or mass assertion.

`characterProduct_one_upperLaplacian` and
`full_path_blockCasimir_carrier`,
`lean/YMGap/Continuum/SU2QuaternionCyclicPathBlockCasimir.lean:75` and
`:183`, differentiate each actual character on its OWN upper endpoint,
then insert the original source and integrate the original lower endpoints.
Each valid full path consequently has its degree's d(d+2) eigenvalue on
each corresponding output block, not merely a total-Casimir eigenvalue.

`literalPair_symm` and `haar_activeCasimir_self`,
`lean/YMGap/Continuum/SU2QuaternionLiteralCasimirPairing.lean:151` and
`:184`, expose existing proved identities without changing types or proofs.
Distinct full degree paths are orthogonal by this original Casimir symmetry,
strict separation of d(d+2), and rational cancellation. This is derived,
not a new orthogonality assumption. `full_path_heat_pairing`,
`lean/YMGap/Continuum/SU2QuaternionCyclicPathHeatEigen.lean:149`, expands
the actual supported test tree and reassembles its surviving equal-degree
terms. It identifies the original full heat attenuation under EVERY
supported Haar test, without a nome or cutoff guard. It does not assert
equality under arbitrary unsupported tests.

### Actual full-product output energy

`productMap_casimir_grouped`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSmoothing.lean:83`, proves
the exact output energy sum over the ORIGINAL input-dependent ragged tree:

    H[(P_full p)*C(P_full p)]
      = sum_paths totalCasimir(ds)*attenuation(ds)^2*H[p*pathPiece(ds)].

The original complete-path input masses are already proved nonnegative by
`full_path_pairing_nonnegative`,
`lean/YMGap/Continuum/SU2QuaternionCyclicDiagonalRemainder.lean:70`.
No signed coefficient norm or supplied spectral decomposition replaces
them. `productMap_angular_smoothing`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSmoothing.lean:123`, therefore
proves for every supported signed input, every cutoff and 0<=w<=1:

    h*Angular(P_full p) <= H[p*P_full p].

The RHS remains the original uncentered Haar heat pairing at this stage.

### Original spatial source, inactive coordinates and terminal recursion

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSmoothing.lean`.
`transferStep_projected_full_heat`, line 77, retains the COMPLETE source
V*f and integrates it on genuinely inactive fringe blocks. Proved original
geometry shows fringe plus active blocks is a permutation of every block;
the projected source is independent of the integrated fringe. Only then
are those absent heat factors restored and the full heat estimate applied.
The identity is under all supported tests, not deletion of action factors.

`transferStep_angular_smoothing`, line 126, uses the original quadratic
pin and Casimir self-adjointness to prove

    h*Angular(T f) <= weightedMass(f*T f) = H[V*f*T f].

Every width, cutoff and supported signed f is included. A literal origin
link proves the finite carrier is nonempty even at width zero.
`terminalMessage_angular_smoothing`, line 157, applies this to the actual
terminal recursion T(g_n)=g_(n+1), obtaining exactly

    h*Angular(g_(n+1)) <= oddMass(n).

The RHS is the SAME original odd-window partition, with the original nome,
cutoff, width and time index. No width/depth factor, inverse heat floor,
large-cutoff guard or division by the partition enters this estimate.

### Remaining causal input and verification boundary

This is UNWEIGHTED output angular energy. The endpoint source still
contains spatial multiplication, and observable energy contains original
centering, products and signed heat defects. Those terms cannot be dropped
or assigned favorable signs by this theorem. Useful control of their
complete combination against SAME interacting variance on a justified
physical scaling family remains OPEN. Nonzero continuum survival, physical
mass, full same-theory QFT and every compact simple group remain OPEN.
No canonical field, chart status or frontier statement was changed.

Six final focused file checks passed 22 printed axiom gates: 15 newly
public/new and seven existing, all within {propext, Quot.sound}. No new
sorry, axiom, Classical dependency, native_decide or noncomputable
declaration. Independent Sol/Luna reviews confirmed full action retention,
inactive-coordinate integration, parameter scopes, terminal time index and
the absence of an interacting-variance claim. Initial namespace, rational
zero and per-slot elaboration errors were repaired without changing the
mathematical statements or raising limits.

Main alone compiled serially through the safe-build skill's monitored
launcher: one worker, mandatory 20 GiB ceiling, 12 GiB OS reserve and
dynamic telemetry. Preflight found 84 percent pressure-free memory, zero
swap and no competing compiler/test/runner. No broad root/tree build,
full axiom audit or guard ran; root imports are registration only. CI
remains manual-only. The unchanged canonical ASCII chart was not printed.

Accepted log SHA-256 values:

- `/tmp/ym-product-casimir-scalar-repaired-20261001.log`:
  `ecaa25726f8e1048d04228e0b70fddfdc47390a5a8d443a858635ef6f8ca7593`.
- `/tmp/ym-path-block-casimir-final-20261001.log`:
  `6f7a87711cc355446b49b28f6fd6e627412f96d490965167ad49134f7c8f4ad8`.
- `/tmp/ym-literal-casimir-symmetry-20261001.log`:
  `86374348135673e7b248ee95b68113b1c9c63f81714a75b3780763f154ab79e3`.
- `/tmp/ym-path-heat-eigen-final-gates-20261001.log`:
  `71113e1e90a30f5a7eb868f7c6ccf97e101b808567a59e23784499c43ec9c0f5`.
- `/tmp/ym-product-heat-smoothing-20261001.log`:
  `3056f195082f9d1432f9b1d1a285123a1af9f6a5f1cbb6e39adf13e1fdf02e45`.
- `/tmp/ym-original-transfer-smoothing-repaired-20261001.log`:
  `943c56483ab03c0a1e9b0eaa59325ccbb5ce85d01bc663bb950e04af55d6a8c0`.

## Addendum: centered transfer output against the SAME interacting variance

Date: 2026-10-01 UTC. This is a concrete consumer of the full-transfer
smoothing above, with no new analytic hypothesis. Let g=T^depth1,
psi=oddCentered(f), and Z=oddMass(depth), at the ORIGINAL nome, width,
cutoff and odd-marginal mean. All new declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredTransferReserve.lean`.

### Exact centered energy and response quadratic

`centered_transfer_quadratic_pin`, line 65, proves

    E(g,f) + B = Z*Var_odd(f),
    B = H[V*(g*psi)*T(g*psi)].

`energy_shifted`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:130`,
first leaves the ORIGINAL two-slice temporal energy unchanged by centering.
`energy_source_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:81`,
then writes that energy as the actual centered source moment minus its
original active-heat pairing. With q=V*g, the first term is
H[(q*psi^2)*P_active(q)]. `centered_unprojected_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:95`,
pins it to Z*Var_odd(f), with the actual mean, not a raw Haar/q-squared mean.
The original transfer quadratic pin identifies the second term as B.
Only exact scalar cancellation remains. V is present in both endpoint
sources of the kinetic pairing; no fringe-independence premise is needed.

### Angular reserve and normalized actual consumer

`centered_transfer_angular_reserve`, line 113, applies
`transferStep_angular_smoothing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSmoothing.lean:126`,
to the COMPLETE supported signed input g*psi. It proves

    E(g,f) + h*Angular(T(g*psi)) <= Z*Var_odd(f), h=1-w.

`normalized_centered_transfer_angular_reserve`, line 138, multiplies BOTH
terms by the same proved-positive original Z reciprocal:

    normalizedEnergy(f) + h*Angular(T(g*psi))/Z <= Var_odd(f).

`centered_output_angular_le_variance`, line 173, drops only the already
proved nonnegative ORIGINAL normalized temporal energy, obtaining

    h*Angular(T(g*psi))/Z <= Var_odd(f).

The input nonnegativity theorem is `normalizedEnergy_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:97`.
The original Z equals the compact partition with 2*depth+1 transitions,
not an independently normalized mass. No source or variance is inverted.
Every supported signed f, every width and depth (including zero), and
headCutoff(w)<=K are retained for 0<w<1. No family-size restriction,
fringe restriction, added width/depth coefficient or heat-floor quotient.

### Residue and independent review

This supplies the advanced CENTERED OUTPUT/interacting-variance regularity
join. It remains an UPPER budget; no useful positive lower reserve or
scaling-small complete signed endpoint observable-energy bound is proved.
The full spatial multiplication, signed heat/cutoff debt and mean corrections
in that primary physical estimate remain. A chosen physical observable
and justified changing-coupling/spacing family still need useful control.
Survival, physical mass, full QFT and every compact simple group remain OPEN.

The existing width-one completed Wilson-time kernel witness is not silently
identified with T(g*psi) or its finite polynomial angular energy. Review
found no declaration pinning those two objects for this purpose, so no
finite-reserve counterexample is inferred from that witness. Nor is a
positive reserve fraction for every arbitrary polynomial made into a new
canonical requirement. Sol/Luna independently reviewed the centered source,
time index, complete action, normalization and inequality directions.

The final focused file check exited zero with all FOUR printed gates
exactly {propext, Quot.sound}. A missing `haar_of_coeff` namespace was
repaired before acceptance; no mathematical statement or safety limit
changed. No new sorry, axiom, Classical dependency, native_decide or
noncomputable declaration. Main alone compiled with the monitored safe-build
procedure, one worker, 20 GiB ceiling, 12 GiB OS reserve and dynamic telemetry.
Preflight showed 84 percent pressure-free memory, zero swap, and no competing
compiler/test/runner. No full root/tree build, broad audit or guard ran;
the root import is registration only. CI remains manual-only. No canonical
field or chart marker changed, and no unchanged chart was printed.

Accepted final log: `/tmp/ym-centered-transfer-reserve-final-20261001.log`.
SHA-256: `1e65b1d0cc545d49f84aed46d9e44a80d3cdf11a2f46bb6c4949bf0397079cac`.
