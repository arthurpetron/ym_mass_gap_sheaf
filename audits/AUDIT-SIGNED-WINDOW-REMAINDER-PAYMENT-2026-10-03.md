# Original signed-window route and reconstructed-square payment

2026-10-03 UTC. Two focused checks, not a full audit or aggregate build.
The unchanged constructive continuum Yang--Mills/Clay target is OPEN.

## Forward: a genuine SAME-norm payment

Use the ORIGINAL transfer T, spatial action V and weighted integral ell.
For supported signed psi, put

```
h=1-w; A=g_(n+r+1); b=T^(r+1)(g_n*psi); phi=G_k*b
q=P_fringe(V*A)=Vbar*A
Z0=ell(A^2); Z1=ell(A*T A); B=ell(b^2)
alpha=h^2/2; rate=alpha/4=h^2/8
```

`blockConditionalRatio_sourceSquare_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRemainderPayment.lean:68`,
proves H[(q*phi)^2]<=spatialCeiling*B. The actual positive-step fringe
independence of A and phi permits the projected spatial-square comparison;
the finite reciprocal multiplier then gives ell[(A*phi)^2]<=B.
This is an inequality, not Vbar^2=V or a change of carrier or mean.

`original_block_rawSquare_payment`, same file:136, uses the EXISTING
Z0<=P*Z1 comparison to construct

```
Z0*rate*H[(q*phi)^2] <= p*Z1*B
p=rate*P*spatialCeiling
```

`blockRemainderRate`, same file:121, and `blockRemainderPaymentCap`,
same file:130, define the explicit coefficient and fixed-parameter cap.
There is no inverse of B, q or a terminal mass. B=0 is included.
The cap depends on nome/width and is NOT asserted scaling-small or
arbitrarily payable by choosing a later approximation degree.

The complete signed residue remains literal:

```
Residue = -alpha*completedSquare + sourceCubic - sourceOmitted
          - h*pairRemainder(q,q*angularSquare(phi))
ReducedSignedBulk = Z0*(h*(SourceAngular+angularWeightChange)+Residue)
```

These are `signedRemainderResidue`, same file:191, and
`blockRemainderSignedBulk`, same file:237. The sign restoring the original
Taylor difference is PLUS h*angularWeightChange. The generic exact
square-completion identity is
`SU2QuaternionCompleteRemainderSquare.completeRemainder_square_completion`,
`lean/YMGap/Continuum/SU2QuaternionCompleteRemainderSquare.lean:252`.

`sourceDerivativeSignedBulk_remainder_payment`, new file:251, proves the
previous original SourceBulk<=ReducedSignedBulk+p*Z1*B.
`original_block_remainderPaid_cost_relative_tolerance`, new file:310,
then proves D<=ReducedSignedBulk+(p+zeta+delta+epsilon)*Z1*B.
The correction onset is at k, reconstructed source/cost at k+1,
reconstruction onset at k+1 and drift onset at depth n+r, unchanged.
No favorable sign of Residue or direct DV*X cancellation is asserted.

## Backward: aggregate costs suffice for the existing survival ratio

For EVERY state x of the SAME original completion, put C(l)=B(x,T(l)x)
and delta(l)=C(l)-C(l+1). Decreasing first defects give

```
C(2u)-C(4u) <= 2*sum_(t=u..2u-1) delta(2t).
```

`response_window_cost_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:155`, gives
the general start/count estimate. `response_doubling_window_cost_bound`,
same file:172, gives the displayed instance without any analytic premise.
`aggregate_window_macro_ratio`, same file:181, proves that
2*sum delta(2t)<=(1-kappa)*C(2u) implies kappa*C(2u)<=C(4u).
No positive norm or exclusion of boundary time-kernel states is assumed
in these all-state inequalities.

`originalWindowCost`, same file:198, sums the EXISTING finite original
normalized costs. Each lag has its OWN Z0_t*Z1_t denominator. At a common
stage all summands keep the SAME existing OWN mean, action and Wilson
square. `dyadicWindowCost`, same file:202, and `dyadic_window_pin`, same
file:206, pin the finite unit-response sum to this completed orbit.

`originalWindowCost_converges`, same file:220, proves the fixed-member
finite-sum limit originalNorm*sum delta(2t). The source limits are
`originalOwnBlockCost_converges` and `originalOwnBlockVariance_converges`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157`
and `:136`, respectively. Nome, width, square and finite lag window remain
fixed during this limit; no changing-family interchange is claimed.

`original_window_budget_macro_ratio`, new window file:245, consumes

```
2*sum_(t=u..2u-1) originalOwnBlockCost(stage,t)
  <= (1-kappa)*originalOwnBlockVariance(stage,u), for every stage>=onset,
```

and produces the EXISTING unit-response ratio kappa*R(2u)<=R(4u).
Only the already-constructed pointwise positive originalNorm is canceled,
AFTER the fixed-member limit. With side=2u, this is the input to
`halfAnchorPreimage_norm_cleared` and `normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:115`
and `:132`. Their positive-kappa hypotheses remain obligations.

## Verification boundary

| Focused checked source | Accepted log | Printed gates |
| --- | --- | --- |
| `BF4WilsonAllNomeWindowSignedCost.lean` | `/tmp/ym-window-signed-cost-20261003-2.log` | 9 |
| `BF4ExactSlabFixedSpatialBlockRemainderPayment.lean` | `/tmp/ym-block-remainder-payment-20261003-2.log` | 8 |

Both exited 0. All 17 public gates report dependencies contained in
{propext, Quot.sound}; no sorryAx, errors or warnings in the accepted logs.
Each run used the monitored launcher with jobs=1, 20-GiB worker cap,
12-GiB OS reserve and 300-second status interval. Fresh preflights found
75--76% free memory, zero swap and no competing Lean worker.
Independent cross-reviews passed both mathematical joins. Root imports
are registration only. No sorry/axiom/frontier field/CI/chart change.

Source SHA256:

- Remainder payment: `99e81161fa0be255a43a0f033a76dc0cca62ff74cd800b08d9f44d049756c98b`
- Window cost: `0ee731d82124fd9f8e45152383d0d1a9e0693e2517c65bb53dde80230a292527`

## Remaining mathematical input

The joint normalized signed-window budget on a JUSTIFIED growing-square,
changing-parameter family is OPEN. The new payment cap must be included;
it has no proved useful scaling behavior. A sufficient per-lag relative
bound remains available, but is no longer a necessary intermediate target.
Only complete normalized response drops telescope: raw source, terminal,
Taylor and derivative-square terms have different chronological partitions
and do not inherit that identity. Physical calibration, nontrivial
continuum survival, full SAME-theory QFT axioms, every compact simple group
and the Clay theorem remain OPEN.
