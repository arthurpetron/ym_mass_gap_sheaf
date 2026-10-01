# Original complex physical imaginary shifts and Cayley operator

Date: 2026-10-01 UTC. Continuation after `f0e468a`.
PROVED: actual two-sided imaginary shifts and complex-linear unitary Cayley map.
Fixed strict nome and literal width; original lattice-time units only.

## Actual construction, not a supplied analytic interface

Write R=(I+A)^(-1), J=I-R and D=R^2+J^2, where A is the EXISTING
physical bond derivative, not a heat-bath generator or freely chosen operator.
The preceding milestone constructs D^-1 with original range witnesses and
explicit geometric approximation moduli. The new modules consume that object.

`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSImaginaryShifts.lean:87`
`output_resolventDomain` proves output(Dom x)=Jx from the actual graph sum.
`complement_add` at :103, `complement_sub` at :120 and
`resolvent_complement` at :137 give original rational linearity and RJ=JR.

For x=(x1,x2), put yi=D^-1 xi. The actual graph preimages are:

    plusDomain(x)  = (Dom(Ry1+Jy2), Dom(Ry2-Jy1))
    minusDomain(x) = (Dom(Ry1-Jy2), Dom(Ry2+Jy1)).

Here Dom is `BF4WilsonAllNomeBondOSResolvent.resolventDomain` at shift one;
each component is an ORIGINAL `BondOSDerivative.Domain` class. No representative,
domain witness, inverse or convergence certificate is assumed or selected.
The complex carrier is the EXISTING `ComplexBondCompletion`, with i(a,b)=(-b,a).
`plus` at :142 and `minus` at :145 are literally input+i output and input-i output.
`plusDomain` at :148 and `minusDomain` at :152 construct those objects as data.
`plus_right` at :157 and `minus_right` at :175 cancel the off-diagonal RJ terms,
then apply the actual square denominator pin and its right inverse.

## Full physical pairing and unique inverse

`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSCayley.lean:106`
`eq_of_pairings` proves faithfulness using ONLY physical tests (z,0) and (0,z).
The real self-difference remains in the physical carrier; original completed
positive definiteness identifies it with zero. Ambient arbitrary-vector
pairing tests are not silently substituted for these physical tests.

`shift_pairing` at :154 expands BOTH Hermitian coordinates. Original real graph
symmetry cancels all signed cross pairings, proving

    inner(plus d, plus e) = inner(minus d, minus e).

Opposite-shift surjectivity and physical pairing faithfulness show that equal
plus images have equal minus images and conversely. Averaging their components
recovers the original graph inputs, whose injectivity identifies the domain
classes. `plus_injective` at :220 and `minus_injective` at :226 prove this.
`plus_left` at :232 and `minus_left` at :235 give the actual left inverse laws.

## Same-carrier complex unitary map

`cayley` at :239 is (I-iA)(I+iA)^(-1), and `inverse` at :242 is its opposite.
`inverse_right` at :244 and `inverse_left` at :248 give BOTH inverse laws on
EVERY completed complex physical bond class. `pairing_preserved` at :253 is
full Hermitian equality, not just a real diagonal bound. `pairing_inverse`
at :257 identifies its actual adjoint action.

Surjective original pairing tests also prove `cayley_add` at :265 and
`cayley_smul` at :273. Full complex scalar linearity retains BOTH supplied
CReal QCauchy witnesses. No independent linearity assumption for D^-1 is used.
The map and inverse are actual functions returning states, not erased existence
assertions or new canonical frontier fields.

## Exact scope and next causal frontier

This constructs fixed-parameter unitary OPERATOR structure on the same
physical carrier. It does NOT construct a continuous unitary time group,
identify a continuum Hamiltonian or its spectrum, calibrate physical time,
improve the strict transfer rate, or prove a physical mass gap.

The independent analytic review identified no near-one response producer in
the current source/order/channel estimates. The PRIMARY missing estimate is
control of signed centered increments under the ACTUAL edge law
K_w(x,y)q(x)q(y), q=V_w*T_w^(n+1)1, relative to the SAME Z*oddVariance,
along a justified changing-coupling/spatial/spacing family. The existing
response fraction w^12*(localLower/localUpper)^2 is not a proved near-one
fraction. Its actual source and cleared SAME-variance budget are written in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:180`,
`padded_family_energy_band_cleared`; `familyResponseFraction` is at :165.
Output smoothing does not supply that comparison.

Useful signed scaling, nonzero continuum survival, physical mass calibration,
canonical continuum OS/QFT, Yang--Mills field/UV identification and every compact
simple group remain OPEN. No canonical field, guard or displayed chart marker
is changed; the unchanged ASCII chart is not reprinted.

## Focused verification boundary

Both final focused checks exited zero, emitted dependency oleans and passed
all 11+14=25 printed axiom gates, each exactly {propext, Quot.sound}.
No sorry, new axiom, Classical, native_decide, noncomputable declaration,
new analytic assumption, canonical field/guard change or surrogate was added.
Independent Sol mathematical review found no sign, carrier, domain-witness,
pairing-test or linearity defect. Luna independently checked every final gate
name/count/dependency, source scope and both log hashes. Neither ran a compiler.

Main alone checked through the monitored safe-build procedure: one worker,
explicit --check-worker-limit-gib 20, 12 GiB OS reserve and dynamic telemetry.
Initial checks exposed nested-comment, scalar eqv composition, rewrite-target
and dependent-expression whnf issues; all were repaired before acceptance.
A local two-million-heartbeat diagnostic attempt still timed out. The final
proof instead keeps scalar cancellation in private opaque RC lemmas, and the
accepted Cayley check uses the DEFAULT heartbeat budget and takes 4.2 seconds.
Worker/memory limits and launcher configuration were never raised or weakened.
Preflight and final telemetry found 84 percent pressure-free memory and zero
swap. Failed logs are not proof evidence. No broad build/audit/guard or CI change
is claimed. Root imports are registered, not checked in aggregate.

Accepted logs and SHA-256:

- `/tmp/ym-complex-bond-imaginary-shifts-preimages-accepted-20261001.log`:
  `eba54a9b490c77886018d4b6d02df0cc557e05f876a9629aead4b64478b8a631`.
- `/tmp/ym-complex-bond-cayley-opaque-20261001.log`:
  `9cddbe42cb46bfc22d075d97c0941284215e4b040114791f553f73a7218c0e4d`.
