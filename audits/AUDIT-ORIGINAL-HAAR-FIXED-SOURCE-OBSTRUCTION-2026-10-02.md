# Original Haar witness against universal signed quartic transport

A constructed norm-one original Haar source now gives a negative quadratic
for the proposed squared-nome affine quartic majorant. One fixed source
works at EVERY sufficiently large cutoff, not merely at a moving prefix
edge. This prunes a universal transport shortcut; the estimate for the actual
interacting Wilson source remains OPEN.

## Explicit original source and its norm

`endpoint`, `lean/YMGap/Continuum/SU2HeatQuarticSignedHaarObstruction.lean:70`,
is an explicitly specialized original solid character. `endpoint_supported`
at line 72, `endpoint_degree` at line 87 and `endpoint_harmonic` at line 90
prove its one-link support, exact degree and zero head Laplacian.
`endpoint_norm` at line 250 proves its ORIGINAL one-link Haar squared norm
is exactly one, using harmonic reproduction and partial-head integration.
No free character-packet norm is substituted.

Retained-coefficient specialization does not permit deleting padded monomial
zeros as coefficient equalities. The proof preserves those coefficients;
only proved original arbitrary-insertion Haar-carrier equalities perform
the necessary recodings. Both physical endpoint links remain Haar variables.

`character_response_pin` at line 308 proves the exact general bilateral
selection `(n+1)*Gamma(n,j)=if j=n then 1 else 0`.
`characterRow_quadratic_pin` at line 355 extracts any finite original
relative-character row coefficient, with no coefficient-sign hypothesis.

## Actual residual quadratic

`affineResidual` and `affineQuadratic` in
`lean/YMGap/Continuum/SU2HeatQuarticSignedHaarObstruction.lean` are the literal
relative kernel and its actual original Haar insertion, with

    residual = c*H(q*q,K) + e - chord^2*H(q,K).

`affineQuadratic_cleared_pin` at line 435 gives
`(K+3)*quadratic=-coeffW(q,K)` on the constructed degree `K+2` endpoint.
`affineQuadratic_negative` at line 474 proves negativity for EVERY `q>0`,
EVERY K and arbitrary c,e, including all head-guarded cutoffs.

## One fixed source works at every later cutoff

`quarticCoeff_interior`,
`lean/YMGap/Continuum/SU2HeatQuarticFixedSourceObstruction.lean:47`, proves
that `n+2<=K` retains the whole original five-band coefficient stencil.
`affine_interior_pin` at line 104 then gives the exact original quadratic

    (n+1)*quadratic = c*coeffW(q*q,n)-quarticCoeff(coeffW(q),n).

`fixedSource` at line 142 sets `n=fullCoefficientCutoff(q,c)`. It depends
on q,c, NOT on K or e. `fixedSource_supported` at line 144 and
`fixedSource_norm` at line 147 provide actual one-link support and original
norm one. `fixedSource_negative_all_later` at line 174 proves negativity
for `0<q<1,c>=0`, EVERY `K>=n+2` and EVERY constant e, using the checked
full-coefficient inequality. No uncut operator limit is asserted.

The positive-source pointwise Haar certificate is unaffected: pointwise
kernel positivity does not imply positive quadratic pairing on signed
bilateral endpoints. Neither witness is claimed to be the literal Wilson
endpoint source, to have its interacting mean, or to refute its desired bound.

## Concrete open finite comparison

For the actual dyadic square expression e, let f=`sourcePolynomial e`.
The signed source is instead `sourcePolynomial(filteredExpression e)`;
its window depths are `(t-1,2,t)`, with `t>=1`. `windowRatio`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean:132`, and
`oddVariance`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:87`,
use the same original terminal-pair partition Z at depths `(t+1,t)`.
`originalWindowScalar_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:123`,
pins that signed window. The original normalized energy also uses this Z:
`finiteEnergy`, `lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:90`.

Write S for the signed unnormalized window numerator, E for the original
unnormalized energy, M and V2 for the original odd marginal first and second
moment numerators, and Vnum=V2*Z-M*M. The next paired estimates are OPEN:

    E*Z <= (1-reserve)*Vnum,
    (lag-1)*S*Z <= 2*(reserve-gamma)*Vnum,  gamma>0.

These must hold along the justified family and the required regulator tails,
or with controlled normalized slack. Dividing by the SAME positive Z squared
gives the reserve and filtered budget. Source/variance/energy limit pins and
computed rectangle moduli already exist; no new transport structure is needed.
This records algebraic alignment, NOT a proof of either quantitative estimate.

## Verification and project scope

The final two focused checks exited zero and passed 14+6=20 public gates,
each within `{propext,Quot.sound}`. Independent mathematical review passed.
First attempts rejected missing namespaces and false coefficient-level padding
identities; repairs used the original Haar carrier, not new axioms or limits.

| Artifact | SHA256 |
| --- | --- |
| `SU2HeatQuarticSignedHaarObstruction.lean` | `84ac1fc98e7a0e9bb451142c7304062ff705c643defe082a7e9df38d7f110855` |
| `SU2HeatQuarticFixedSourceObstruction.lean` | `b42815b6e344a7847edbd109bfcb5a0d885fa3689eb7a21a971cb51c820241a7` |
| `/tmp/ym-quartic-signed-haar-obstruction-20261002-third.log` | `25e2873e3ab8e21079f7df1e8b3e9d4366173ce571c1bfcb0a09739c0ef8c01e` |
| `/tmp/ym-quartic-fixed-source-obstruction-20261002-second.log` | `525d9a934c6351891467bef9ed11d983ee62465d2562c48321c92b9290e5e5e7` |

One heavy worker, explicit 20-GiB ceiling and 12-GiB OS reserve; fresh
preflights showed 83--86 percent pressure-free memory and zero swap. Two root
imports registered, NOT aggregate-checked. No broad build/audit, new sorry,
axiom, classical shortcut, weakened field, surrogate carrier or CI change.
The canonical chart fence SHA256 stays
`6f64d1437f38622c455b8d123f001def2a5c459eebf9e785b3e40d117b19a179`;
no exact displayed claim changed and the chart is not reprinted.

Spatial/spacing control, useful family costs, continuum survival, physical
mass calibration, full SAME-theory QFT, every compact simple group and the
Clay target remain OPEN.
