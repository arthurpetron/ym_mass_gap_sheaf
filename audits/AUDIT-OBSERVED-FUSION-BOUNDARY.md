# Signed observed-source fusion on the original partition

Date: 2026-09-17. Source baseline `843ac19`; parallel independent inputs
were checkpointed separately in `ca302b1`.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4,
for every compact simple group, with same-theory QFT axioms and finite
positive physical Hamiltonian mass gap. **OPEN.**

## New coverage and exact meeting point

The earlier fusion estimate used an unobserved terminal source. The new
source is f=observedMessage(w,K,width,m,Lleft,p), which can have either
sign and share variables with the selected face. Its original comparison
message is g=g_(m+Lleft), not a new normalized or observed partition.

`observedMessage_comparison`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialObservedFusionSource.lean:175`,
constructs certificates a*g+f and a*g-f from the actual left-window
interval. `retainedMessage_comparison` at line 136 combines them with the
signed edge interval d+e, d-e using

    2*(a*d*g+f*e) = (a*g+f)*(d+e)+(a*g-f)*(d-e)
    2*(a*d*g-f*e) = (a*g+f)*(d-e)+(a*g-f)*(d+e).

The original positive remaining spatial product R multiplies every term,
then the original kinetic map is applied. No independence or positivity
of f or e is assumed. The resulting reference is the existing erasedMessage
of g; the previously proved single-face floor compares its partition with
that of the ORIGINAL U=Tg.

`retainedMessage`, same source file:61, is Kinetic((R*f)*probe).
`signedSource_fusion` at line 219 proves for every rational nome and cutoff,
including zero, and every physical selected spatial face:

    T(f*chi_1)-c_1*T f = B+E,
    B=Kinetic(R*f*bulk), E=Kinetic(R*f*edge).

This is the necessary correction to the unobserved special case: T f is
not T g. Define J(h) and Z(h) by the actual right-window input numerator
and partition, and D(h,U)=J(h)*Z(U)-Z(h)*J(U). Then

    D(T(f*chi_1),U)-[c_1*D(Tf,U)+D(B,U)] = D(E,U).

This is `observedFusion_error_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialObservedFusionBoundary.lean:103`.
`observedFusionError` at line 61 defines exactly the left side. Every
term uses the SAME original reference U, right action and terminal message.
The c_1*D(Tf,U) term cannot be silently cancelled or treated as independent
of the bulk. No subunit bound on c_1 is assumed.

## Quantitative consequence

With actual interval caps a and c for the left and right windows, every
0<w<1 and K>=headCutoff(w), `observedFusion_bound`, same file:153, proves

    headFloor(w)*abs(observedFusionError)
        <= 2*(a*c)*boundaryCap(w,K)*Z(U)^2.

The source certificates above fill the inputs to
`inputCovariance_relative_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedInputBound.lean:168`.
The auxiliary comparison partition cancels through
`originalMessage_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceRemainder.lean:248`.

`observedFusion_small`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialObservedFusionBoundary.lean:234`,
uses the already computed `relativeBoundaryCutoff(w,a*c,epsilon)` to prove

    abs(observedFusionError) <= epsilon*Z(U)^2.

Its cutoff is independent of width, both boundary depths and both window
lengths FOR FIXED certified caps and nome. No nome-uniformity is asserted.
The factor 2*a*c+1 used by the existing tolerance includes zero caps.
Messages, action and partition may change with K; this is relative error
control, not raw unnormalized convergence.

## Residue and nonclaims

This is genuinely new coverage of an earlier signed observed source, with
an endpoint fundamental insertion. Merely propagating the former boundary
error through extra future steps could already be handled by positive-order
preservation or the arbitrary right window; that alone would not supply
a new decay estimate.

The coupled baseline c_1*D(Tf,U) and bulk D(B,U) remain analytically
uncontrolled beyond the existing small-nome or width-dependent routes.
No repeated-fusion contraction, all-time full Wilson-orbit decay, spacing
family, continuum QFT, physical mass or all-group conclusion is supplied.
The next estimate must retain these signed terms and their original
normalization. No new assumed frontier structure or analytic oracle is added.

## Verification

Both new modules passed focused serialized one-worker/20 GiB checks through
`scripts/safe_lean_build.py`, with process/swap preflight. All nine printed
public gates lie within {propext, Quot.sound}; no sorry introduced or
discharged. Two semantic-root imports added; root/full-tree/full audit,
guard and progress runs NOT performed. CI and resource configuration
unchanged. Parent inspected both full sources.
Independent read-only mathematical review also passed the signed source,
two-cell products, retained action, extra baseline term, original partition
and fixed-cap cutoff dependence; it confirmed the stated iteration boundary.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-observed-fusion-source-20260917.log` | `338b2feca90eca6263f20ee7aded36b927cc958d1ab79237905d2e01e657bba3` |
| `ym-observed-fusion-boundary-20260917.log` | `7d73a0978da1dbd01218fc4805a4756219c55cda07cb468fc3955115cfed5fec` |
