# Retained original companion and observable-weighted source loss

The whole-project target remains OPEN: constructive continuum Yang--Mills
on R^4 for EVERY compact simple group, with SAME-theory full QFT axioms,
nontrivial survival and finite positive physical Hamiltonian mass.
This checkpoint concerns exact finite SU(2) quantities only.

## Forward construction: retain the discarded square

For the SAME signed source q, literal Wilson observable f and positive
two-copy heat W, let dq=q-q', df=f-f', and write H2 for two-copy Haar:

```
I = H2[W*dq^2*df^2]
J = H2[W*dq^2*(f+f')^2]
D = H2[W*dq^2*(16-(f+f')^2)]
O = H2[W*dq^2*(4-f^2)].

I+J = 4*singleEndedCost(f,q)
8U+I+J = 4(Q+R)
J+D = 32*heatLossPair(q,q)
D = I+4O.
```

Definitions: `sourceCompanionCost`, `sourceCapDeficitCost`,
`sourceObservedLoss`, respectively
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceCompanion.lean:54`,
`:61`, `:70`. Exact identities: `increment_add_companion_pin` at `:168`,
`eight_sourceMoment_add_increment_companion_pin` at `:304`,
`companion_add_capDeficit_heatLoss_pin` at `:349`, and
`capDeficit_eq_increment_observedLoss_pin` at `:234` in that module.
The equalities need no source sign, cap or positive-credit guard. Positivity
of J, D and O uses the actual positive heat; D/O also use the literal cap
four certificate. It is not a variance-comparison hypothesis.

The ACTUAL original terminal spectator channels are constructed in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareCompanionDeficit.lean`:
`squareChannelCompanion` at `:61`, `squareChannelCapDeficit` at `:70`,
`squareChannelObservedLoss` at `:80`. The original-channel identities are
`squareChannelCompanion_add_capDeficit_heatLoss_pin` at `:148`,
`squareChannelCapDeficit_eq_increment_observedLoss_pin` at `:186`, and
`paddedSquare_rawSecond_increment_companion_pin` at `:239`.

## Backward join: the actual chronological cost and OWN Ward identity

Set per=4*side, a=w^(12*side), beta=w^(32*side), k=2a-1-beta,
h=1-w^(4*side), F=a*(1-beta)-4k. Let M be the actual channel mass,
Z the original odd partition and U the original unnormalized raw moment.
`paddedSquare_energy_companion_capDeficit_pin`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareCompanionDeficit.lean:327`, gives

```
(1+beta)*(4e+I)+(k/2)*I
  = 4F*M + 4k*(4Z-U) + (k/2)*D.
```

The unweighted linear L=M-Z term is eliminated by retaining D, NOT by
proving D small. The existing exact scalar bound F<=36h^2 and original
angular pin give the normalized angular payment in
`paddedSquare_energy_companion_quadratic_angular_payment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareCompanionPayment.lean:71`.
The quadratic ceiling is **144*per*h^2*(M/Z)**, not 144*per*h^2.
No useful bound on M/Z is supplied.

`originalOwnBlockCost_companion_quadratic_ward_boundary_paid` at `:173`
in that module joins the SAME chronological Cost and OWN Ward identity.
ONLY boundary drift is paid; stage OWN center, BOTH partitions, COMPLETE
Signed, raw reference and endpoint OWN variance remain unchanged.
`originalOwnBlockCost_observedLoss_quadratic_ward_boundary_paid` at `:276`
then substitutes D=I+4O and cancels the matching kI/2:

```
per*(1+beta)*(4Cost+I/Z) + 4k*Ward_norm
 <= 144*per*h^2*(M/Z) + 12*per*k*endpointOWNVar
      + 2*per*k*(O/Z) + 4*per*(1+beta)*(eta*RawRef+Signed).
```

Thus the extra kI/2 is NOT independently paid credit. These new identities
and scalar ceilings need no k>=0 guard; interpreting k times a positive
square as favorable credit still requires it. No Ward or Signed sign is
asserted. Endpoint OWN variance is not the surviving filtered-start norm.

## Precise remaining analytic input

The next target is useful JOINT control of
`2*per*k*(O/Z)-4*k*Ward_norm`, endpoint OWN variance, the mass-weighted
quadratic scalar ceiling and COMPLETE chronological Signed/paid raw-reference
drift against the SAME surviving filtered-start variance on a justified
changing family. No such estimate is supplied here. O is an observable-
deficit-weighted source jump loss, not the marginal angular moment controlled
by OWN Ward. `paddedSquare_block_gamma`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean:203`, identifies
the literal cap deficit with selected-link angular geometry, but does not
bound this source-jump insertion.

The actual backward consumer is `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
Its eventual ORIGINAL cost-versus-filtered-variance input remains OPEN;
it is neither assumed here nor recovered by the circular substitution
Signed=Cost-(energy+drift). Scaling, survival, physical mass, SAME OS/full
QFT/continuum and every-group/Clay remain OPEN. Supporting A03 only:
the exact displayed chart claims have not changed, so no chart reprint.

## Independent mathematical review: this is not coercivity

The reviewer expanded O using the SAME channel heat marginals and literal
square heat image. With D0=4Z-U and Aheat=1+beta, the expansion is
O=(7+beta)M-Aheat*Q-2D0. OWN Ward gives
Ward_norm=per*(3*endpointOWNVar-D0/Z). Substitution into the displayed
payment cancels its endpoint variance term and returns the existing exact
energy identity `paddedSquare_channel_exact_cost`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:181`.
The scalar quadratic ceiling adds nonnegative slack; it is not independent
control of the source-coupled remainder. This expansion is an algebraic
review finding, not a separately kernel-checked new theorem in this module.

Consequently this checkpoint retains useful exact information but supplies
NO new coercive cost-versus-variance estimate. Stop extending identity-only
consumers. The next work must prove independent original-action control of
the channel cap-deficit moments relative to interacting variance, or signed
chronological cancellation reaching the SAME filtered norm. Neither is
supplied by the new identities or ordinary OWN Ward substitution alone;
no independent bound was found in the inspected terminal recurrence APIs.

## Verification boundary

Three final serialized focused targets exited 0; all TWENTY-TWO public
definition/theorem gates report exactly {propext, Quot.sound}. Accepted logs
contain no warnings or errors. Earlier failed elaborations are NOT accepted
evidence. Independent mathematical and same-object source reviews passed;
the non-coercivity finding above is included rather than treated as closure.

| Accepted log under `/private/tmp/` | SHA256 |
| --- | --- |
| `ym-source-companion-observed-20261004-1.log` | `f15efd4c38137e5eddfdcda833538288ed16ebedc05bb9b5c01492db1197da16` |
| `ym-actual-channel-companion-20261004-5.log` | `6cbe0f5cd24633ad3c736bf120435caaa87642172a5014c3597b9f95449cfdbb` |
| `ym-original-companion-payment-20261004-3.log` | `463a716899397cfea6e4d1aba1b0687101a672aedc30948d16d5ee01cd9a5193` |

Frozen source SHA256, in generic / actual-channel / consumer order:

```
f82d23de4f7d15811a9249bf43bad0e9169267457176f4a28daf3e6d85b35e05
21a468bfda2303791b00b6adca64f45e5c104bc2a2fc032af6152bc118a705fc
a74a7907ff8d70ede92e984d5e3ccca5b00acf9d2a6afed125318d6fdd8e0d44
```

Each check used one monitored 20-GiB worker and a 12-GiB OS reserve, with
fresh process/pressure/swap preflight. Final preflights showed 75--76% free
memory, zero swap and no competing compiler. No new sorry/axiom/Classical/
native_decide, analytic budget, weakened frontier, raised resource limit or
CI change. Local opacity and explicit scalar pins solved the elaboration
timeouts without raising limits. Root import is registration ONLY, not root
verification. No full/root build, broad audit, guard or metrics run.
The whole-project goal remains ACTIVE and OPEN.
