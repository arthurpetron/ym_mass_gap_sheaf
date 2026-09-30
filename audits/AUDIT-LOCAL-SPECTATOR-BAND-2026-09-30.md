# Original terminal endpoint: local spectator band

## Whole-project goal and scope

The goal remains a constructive continuum Yang--Mills theory on R^4 for
every compact simple group, with the same-theory QFT axioms, nontriviality
and finite positive physical mass gap. This checkpoint constructs a finite
SU(2) input to the nontrivial-survival branch. It does not close that branch
or the separate signed decay estimate. No canonical chart state changed.

## Checked mathematical result

Write V for the original spatial weight and u_n for its actual terminal
message. For a supplied finite link list S, split only the final kinetic
factors and the spatial faces incident to S. The constructed polynomial is

    A = V_complement * P_rest(V * u_n).

Every earlier action factor remains inside the input V*u_n. The SAME A is
certificate-positive and independent of each selected link in the declared
slice carrier. Both original endpoint comparisons are constructed:

    headFloor(w)^c * headFloor(w)^k * A
        <= V*u_(n+1)
        <= prefixCap(w)^c * prefixCap(w)^k * A,
    c + k <= 7*length(S).

Here c counts incident spatial faces and k counts selected active kinetic
links. Repeated selected links are allowed; the budget merely becomes
looser. A plaquette has four links, so c+k<=28. The inequalities are
positive polynomial certificates on the original Haar carrier, not a new
assumed pointwise-order rule. The nome dependence is explicit; the late
cutoff guard is `headCutoff w <= K`. The endpoint has terminal depth n+1.

The final uniform weakening is also checked, not merely deduced in prose:
for length(S)<=size, `localLower(w,size)=headFloor(w)^(7*size)` and
`localUpper(w,size)=prefixCap(w)^(7*size)` are positive and give the same
certificate bands. Neither scalar names width, terminal depth or cutoff.
For a plaquette take size=4 and exponent 28.

Declaration map (paths below begin at `lean/YMGap/Continuum/`):

| Declaration | Source | Content |
|---|---|---|
| `spatialCollar_partition` | `BF4ExactSlabFixedSpatialLocalCollarGeometry.lean:35` | Exact original-face permutation |
| `spatialCollarFaces_length_le` | `BF4ExactSlabFixedSpatialLocalCollarGeometry.lean:100` | At most six faces per selected link |
| `productMap_localFloorCertificate` | `SU2QuaternionProductHeatLocalBand.lean:128` | Erase a finite prefix, retaining complete input and exterior kernel |
| `productMap_localCapCertificate` | `SU2QuaternionProductHeatLocalBand.lean:168` | Matching cap with precisely the same erased message |
| `spectator` | `BF4ExactSlabFixedSpatialLocalSpectator.lean:140` | Explicit A, not a supplied witness |
| `spectator_independent` | `BF4ExactSlabFixedSpatialLocalSpectator.lean:151` | Selected-coordinate independence with original carrier membership |
| `spectator_certificate` | `BF4ExactSlabFixedSpatialLocalSpectator.lean:238` | Constructed positivity |
| `endpoint_lowerCertificate` | `BF4ExactSlabFixedSpatialLocalSpectator.lean:250` | Original endpoint lower band |
| `endpoint_upperCertificate` | `BF4ExactSlabFixedSpatialLocalSpectator.lean:273` | Original endpoint upper band |
| `plaquette_comparison_count_le` | `BF4ExactSlabFixedSpatialLocalSpectator.lean:305` | Width/depth-independent factor budget 28 |
| `localLower`, `localUpper` | `BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`, `BF4ExactSlabFixedSpatialUniformLocalBand.lean:47` | Explicit nome/size-only scalars |
| `localLower_positive`, `localUpper_positive` | `BF4ExactSlabFixedSpatialUniformLocalBand.lean:49`, `BF4ExactSlabFixedSpatialUniformLocalBand.lean:75` | Positive coefficients |
| `endpoint_localLowerCertificate` | `BF4ExactSlabFixedSpatialUniformLocalBand.lean:189` | Actual width/depth/cutoff-independent lower coefficient |
| `endpoint_localUpperCertificate` | `BF4ExactSlabFixedSpatialUniformLocalBand.lean:203` | Matching upper certificate on the same A |

## Next mathematical consumer: not yet checked

For the fundamental character f, centered probe h=f-m and four ACTIVE
face links, use the spectator-weighted dual b=(w^(-12)*f-m)*A. The next
concrete task is the exact supported-Haar transmission identity

    P(b) = h * P_rest(A).

The existing bare preimage is
`BF4ExactSlabFixedSpatialPlaquetteResponsePositive.dualTest_preimage`
(`BF4ExactSlabFixedSpatialPlaquetteResponsePositive.lean:93`). It cannot
simply be multiplied by A. A source-level proof route was independently
reviewed: preserve A through the four `Propagates.mul_right` steps of
`SU2QuaternionProductHeatPlaquette.selected_pairing`, and finish with
`productMap_pairing`, not the marginal that discards the exterior kernel.

After proving that identity and the local Haar factorization, the proposed
shared-factor argument is as follows. Set Q_A=<A,P_rest A>, let N be the
original response numerator and Z its original odd partition. The band
ell*A<=V*u_(n+1)<=U*A should yield

    D=<V*u_(n+1)*h,Pb> >= ell*Q_A,
    C=<b,Pb> = (w^(-12)+m^2)*Q_A,
    Z <= U^2*Q_A.

The original partition's positivity then implies Q_A>0. Existing exact
kinetic Cauchy--Schwarz (`SU2QuaternionProductHeatDualForm.kineticPair_cauchySchwarz`,
`SU2QuaternionProductHeatDualForm.lean:127`) would cancel the SAME Q_A and
give N/Z >= ell^2/[U^2*(w^(-12)+4)] when |m|<=2. This paragraph is a
reviewed proof plan, NOT a new Lean theorem. The local cost calculation
already exists as `BF4ExactSlabFixedSpatialPlaquetteDualCost.plaquette_dualTest_cost`
(`BF4ExactSlabFixedSpatialPlaquetteDualCost.lean:204`).

Do not use `BF4ExactSlabFixedSpatialResponseDual.responseFloor`
(`BF4ExactSlabFixedSpatialResponseDual.lean:103`) unchanged here: its 1+C
regularization breaks this homogeneous cancellation. Do not drop the four
active-edge premise; the existing fringe time kernel forbids that shortcut.
This would be a fixed-nome positive-response LOWER bound, not an upper
spectral-gap estimate. Its constants do not assert uniformity as w->1.

For the next implementation, the denominator comparison has the exact
positive-certificate decomposition (a=V*u_(n+1))

    U^2*A*P(A) - a*P(a)
      = a*P(U*A-a) + U*(U*A-a)*P(A).

Every summand is certificate-positive using the proved upper band, actual
product-kernel positivity and a>=0. The detector comparison multiplies the
lower-band certificate by h^2*P_rest(A), also certificate-positive. The
remaining factorization uses selected-coordinate independence, not
independence of the original endpoint a. These are unformalized algebraic
implementation instructions, not additional hypotheses.

After those identities, scalar cancellation can avoid division by the test
cost: D^2<=N*C0*Q_A and D>=ell*Q_A give ell^2*Q_A<=N*C0 by cancelling positive
Q_A once. Then Z<=U^2*Q_A gives ell^2*Z<=N*C0*U^2. Normalize only with the
proved positive original Z and the explicit positive scalar C0*U^2.

The constructed A itself depends on width, cutoff and terminal depth. A
uniform comparison constant does not identify these polynomials across
widths or construct a common thermodynamic carrier. Such a passage still
needs the original observable/normalizer comparison and limit moduli. The
band requires no active-edge premise, whereas the proposed inverse-heat
response step does; these are distinct scopes, consistent with the proved
inactive-fringe time kernel.

## Verification and parallel work

Four final focused, serialized checks passed all 36 printed gates within
{propext, Quot.sound}. Exact checked files are the four new modules above;
no full-root/full-tree build, global axiom audit or frontier guard was run.
Logs: `/tmp/ym-local-collar-geometry-20260930.log`,
`/tmp/ym-product-local-band-20260930.log`,
`/tmp/ym-local-spectator-20260930.log`, and
`/tmp/ym-uniform-local-band-20260930.log`.

Luna supplied the collar geometry, Sol the finite-prefix and uniform
certificates, root the original endpoint join, and a separate Sol reviewer
checked the actual action, same-spectator dependence and scope. The final
corrected checks finished in their initial tool calls. Earlier source errors
were corrected without raising resource limits. One worker, 20 GiB compiler
cap and 12 GiB OS reserve were used;
manual long-job polling remains five-minute cadence with continuous automatic
safety telemetry. No new sorry, analytic-estimate hypothesis or custom axiom.
The signed spatial/scaling producer, all-nome spatial limit, continuum
survival, OS/scaling identification and physical mass gap remain open.
