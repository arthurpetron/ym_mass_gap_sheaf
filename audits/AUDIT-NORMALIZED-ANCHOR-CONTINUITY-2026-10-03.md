# Normalized anchor continuity from the relative budget

The SAME normalized positive-time bond excitation now has a computed
real-time continuity modulus independent of its raw anchor norm. The proof
still requires the original relative budget; neither that budget nor a
cross-scale continuum limit is produced.

## Exact objects and hypothesis

Use the original unit excitation u, completed time T and response R.
Let s=side(scale), N=R(2s), alpha its constructed inverse square root,
and z=alpha*T(s)u. All range/bond/vacuum-complement pins remain those of
`BF4WilsonAllNomeDyadicNormalizedBondAnchor`.

The new module is
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean`.
Budget-dependent public estimates retain 0<w<1, s<width and

    m*(R(start)-R(start+1)) <= C*R(start),
    1<=C, 4*C<=m, start<=s<=m, 2<=s.

There is no uniform lower bound on N or R(1) in the hypotheses.

## Relative half anchor and explicit modulus

`preimageReserve` at line 66 computes kappa=(3/4)*(1/4)^(2*C), with its
positivity proof at line 68. `halfAnchorPreimage` at line 168 constructs
y=alpha*T(s/2)u on the SAME completion. `halfAnchorPreimage_pin` at line
171 proves T(s/2)y=z; no inverse transfer is chosen.

`halfAnchorPreimage_norm_cleared` at line 204 proves kappa*B(y,y)<=1.
It uses R(2s)>=kappa*R(s), then alpha^2*N=1, rather than dividing an
absolute increment estimate by N or bounding alpha uniformly.

`normalizedMesh_increment_bound` at line 257 applies the existing positive
anchor dissipation estimate to that actual preimage. Every dyadic increment
t<=s/2*2^(-k) has squared distance <=2^(-k)/kappa.

`normalizedGeometricRadius` at line 279 computes

    delta(C,epsilon) = (1/4)*2^(-(epsilon*kappa).den).

Its positivity proof is at line 282. The factor 1/4 pays the actual dyadic
approximation slack. The radius depends only on C and epsilon, not nome,
width, scale, m, start or N.

`normalizedBond_geometric_real_increment` at line 377 passes this bound
through the EXISTING represented-real increment rows and bond action.
For every represented positive real t with spacing(scale)*t<=delta,
the SAME bond squared distance from z is <=epsilon.
`normalizedBond_geometric_real_forward_increment` at line 399 propagates
the modulus to every forward real-time orbit point by contraction.

Here spacing(scale)=1/side(scale) is assigned geometric spacing. Its
Yang--Mills physical calibration is NOT proved. Cross-scale vector
comparison, convergence of observables, full QFT and a physical Hamiltonian
mass gap do not follow from this conditional within-family theorem.

## Focused verification and remaining input

The final second focused check passed ten printed gates, all contained in
{propext, Quot.sound}; the reserve/radius definitions are axiom-free.
Independent mathematical and source/log reviews check the same objects and
guards. No new sorry, axiom, classical input, weakened field or resource
increase. Root import registered, NOT aggregate-checked; no full build/audit.
CI and the canonical chart fence are unchanged.

The safe launcher used one worker, an explicit 20-GiB worker cap and a
12-GiB system reserve. Fresh preflight found no competing compiler,
85% memory-pressure-free and zero swap.

Accepted log: `/tmp/ym-normalized-anchor-continuity-20261003-second.log`.
SHA256 source/log pair:

    12c3c72b0c001f6bc65095abbb5d64751a7c42ee2c4de7f35cbaae3e2cc14f5e
    a2271ecd4c02eb88a30b482f8f0d40ac17a45b8aba6b55ec5e88d66e8ffc624c

The forward input remains the useful SAME relative budget on a justified
changing family. The next backward input is actual cross-scale comparison
with explicit moduli and original observable/physical-time identification,
not another raw reserve or absolute continuity wrapper. All displayed
scaling and continuum claims remain OPEN.
