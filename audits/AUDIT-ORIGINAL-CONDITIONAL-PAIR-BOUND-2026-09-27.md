# Original conditional residual-pair lower bound — 2026-09-27

## Result

`BF4ExactSlabTwoLinkResidualLowerBound.conditional_residual_pair_lower`
(`lean/YMGap/Continuum/BF4ExactSlabTwoLinkResidualLowerBound.lean:68`)
proves, for every completed vector `x` of the original full-action carrier
and every ordered pair of physical links `left,right`,

```text
⟨x-P_left x, x-P_right x⟩_F
  ≥ - e (‖x-P_left x‖²_F + ‖x-P_right x‖²_F),
e = (U-L)/(2L),  L=(1-δ)^12, U=(1+δ)^12.
```

The hypotheses are `0<w<1`, `heatRatio w ≤ 1/2`, `δ=heatRemainderBound w<1`, `K≥headCutoff w`, and physical membership of both links in the slab list. There is no distinctness, centering, locality, or assumed conditional-angle premise. The coefficient depends only on `w`, not on `K` or `extent` at fixed nome.

## Proof structure

The actual operator `P` is the original completed conditional link projection.
The reference `Q` transports to the two-link background, applies its coordinate
projection, and transports back. In
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkReferenceProjection.lean`, the exact
declarations are `reference:70`, `conditional_reference:115` (`PQ=Q`),
`reference_conditional:127` (`QP=P`), `reference_idempotent:91`,
`reference_background_adjoint:104`, and `reference_background_norm:109`.
No original-form self-adjointness of Q is asserted. The reference residual
cross term is a nonnegative background square:
`remainder_pair_square` and `remainder_pair_nonnegative` at
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkReferenceEnergy.lean:84` and `:97`.

The completed signed comparison (`TwoLinkSignedComparison.completed_signed_pair`) bounds
`4⟨x,y⟩_F - 2(L+U)⟨Jx,Jy⟩_B0`
above and below by `(U-L)(‖Jx‖²_B0+‖Jy‖²_B0)` for arbitrary completed
vectors (`lean/YMGap/Continuum/BF4ExactSlabTwoLinkSignedComparison.lean:93`).
The remaining exact declarations, all under `lean/YMGap/Continuum/`, are:

| Declaration | File:line | Role |
|---|---|---|
| `two_error_identity` | `BF4ExactSlabTwoLinkResidualIdentity.lean:149` | Original pairing = nonnegative reference term + first error - second error |
| `midpoint` | `BF4ExactSlabTwoLinkPerturbationConstants.lean:25` | Explicit `(L+U)/2` |
| `formError_bounds` | `BF4ExactSlabTwoLinkFormError.lean:105` | Each signed error costs at most `(U-L)/4` times its background norm sum |
| `completed_form_bounds` | `BF4ExactSlabTwoLinkCompletionComparison.lean:147` | `L` times background norm is below original norm |
| `signed_pair_lower` | `RCSignedPairBudget.lean:99` | Combines the signs, reference positivity and original norm comparison |
| `coefficient` | `RCSignedPairBudget.lean:27` | Constructive positive division `(d/2)/L` |
| `pairCoefficient` | `BF4ExactSlabTwoLinkResidualLowerBound.lean:45` | Substitutes `d=U-L` |

The pilot guards are verified by `existingNome_guards` at
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:195`, and
`25U<26L` by `existingNome_pair_calibration` at
`lean/YMGap/Continuum/BF4ExactSlabSmallNomePairCalibration.lean:51`.
These are fixed-nome scalar checks, not a scaling result.

## Verification boundary and next obligation

Nine focused serialized checks passed all 50 printed gates within
`{propext, Quot.sound}`, using one worker and a 20 GiB cap. The modules were
`SU2QuaternionWeightedHaarProjectionCompletion` (9 gates),
`BF4ExactSlabHaarCoordinateLocality` (2),
`BF4ExactSlabTwoLinkReferenceProjection` (12),
`BF4ExactSlabTwoLinkReferenceEnergy` (7),
`BF4ExactSlabTwoLinkResidualIdentity` (2), `RCSignedPairBudget` (7),
`BF4ExactSlabTwoLinkPerturbationConstants` (6),
`BF4ExactSlabTwoLinkFormError` (2), and
`BF4ExactSlabTwoLinkResidualLowerBound` (3).

This is an original conditional-link dynamics inequality, not spatial decay,
an OS time-transfer estimate, a Hamiltonian gap, or continuum closure. The
next steps are ordered-pair summation and constructive `H²`-to-coercivity.
Independent Sol review confirmed both error signs and the factor `2D` for
ordered degree counting. No new analytic hole was introduced. No full build,
full audit, guard run, or canonical-chart change is claimed.

## Next argument selected; not yet formalized

After proving `H² >= gamma H`, use the existing positive finite-volume
centered baseline only to remove a tail, not as the final uniform coefficient.
Take `N=max(1, number of physical links)`, `s=1/(2N)`, `T=I-sH` and
`E(x)=<Hx,x>`. The reviewed elementary route is:
`E(Tx)<= (1-s*gamma) E(x)`, while
`||x||²-||Tx||² <= 2s E(x)`. Their direct telescoping consequence is
`(gamma/2)*(||x||²-||T^n x||²) <= E(x)-E(T^n x) <= E(x)`.
The baseline and geometric energy contraction control the one remaining
norm tail, giving `(gamma/2)||x||² <= E(x)`. The baseline's volume dependence
enters the tail modulus, not the proposed final coefficient.
This deliberately targets a sufficient positive coefficient, not the sharp
gamma, and requires no inverse square root or spectral theorem. None of
these new iteration/telescope inequalities is claimed kernel-checked here.
