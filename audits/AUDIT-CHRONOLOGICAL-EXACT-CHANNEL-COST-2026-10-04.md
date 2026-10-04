# Exact channel payment reaches the original chronological cost

The focused check passed. The whole-project Clay target remains OPEN:
nontrivial continuum Yang--Mills on R^4 for EVERY compact simple group,
with SAME-theory full QFT axioms and finite positive physical mass.
This increment supplies a finite SU(2) connection, not the analytic window
estimate or a justified physical scaling family.

## Forward/backward meet

The backward consumer is `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
It requires eventual
`2*originalWindowCost(stage,u,u)<=(1-kappa)*originalOwnBlockVariance(stage,u)`.
The literal cost and filtered variance are `originalOwnBlockCost` and
`originalOwnBlockVariance`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98`
and `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`.

For K=headCutoff(w)+stage and i=stage+t, the new connection preserves

```
F   = literal long padded Wilson square,
c   = ORIGINAL stage OWN middleRatio(stage+1,stage,F),
psi = F-c, A = g_i, b_t = T^t(g_stage*psi),
Z0  = ell[A^2], Z1 = ell[A*T(A)] = oddMass(i) up to proved equivalence,
Cost_t = clearedRayleighCost(A,b_t)/(Z0*Z1),
D_t = boundaryDrift(A,psi)/(Z0*Z1),
S_t = COMPLETE signedMultiplicationCost(A,b_t,psi)/(Z0*Z1),
R_t = ell[A^2*psi^2]/Z0, eta_t = comparisonEta(i-1).
```

Only positive original partitions are cancelled. The center in b_t, D_t
and S_t is NOT changed to the endpoint center. Shift invariance is applied
only to energy. The original split and terminal drift estimate are
`original_block_rayleigh_split` and `boundaryDrift_terminal_abs_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244`
and `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:271`.
They now give `Cost_t = E_i+D_t+S_t` and `D_t<=eta_t*R_t`.

Forward, insert `paddedSquare_energy_exact_variance_payment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareExactVariancePayment.lean:50`.
For i>=1, K>=2 and explicit k=2*w^(12*L)-1-w^(32*L)>=0:

```
Cost_t + I_i/(4*Z1) + (k*rho/2)*OWNVar_i
 <= ((1-w^(32*L))/2)*M_i/Z1 + eta_t*R_t + S_t.
```

I_i is the ENTIRE original channel increment, not just its response-square
floor. M_i, OWNVar_i and rho are the SAME endpoint quantities of the
existing exact payment. No Taylor/cubic/omitted-mode estimate is introduced.
The endpoint OWN variance, raw reference R_t and filtered norm
`ell[b_t^2]/Z0` are THREE distinct quantities. None is identified with another,
and no source or excitation norm is inverted.

All declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean`:

| Declaration | Line | Checked content |
| --- | --- | --- |
| `originalBoundaryDrift` | 137 | Actual normalized signed boundary term. |
| `originalReferenceSquare` | 141 | Raw endpoint square using the stage center. |
| `originalOwnBlockCost_energy_split` | 149 | Literal normalized chronological split. |
| `originalBoundaryDrift_upper` | 204 | Computed eta times raw reference, not filtered variance. |
| `originalOwnBlockCost_exact_channel_payment` | 237 | Exact payment enters actual cost with BOTH corrections. |
| `originalOwnBlockCost_exact_channel_boundary_paid` | 276 | Boundary drift bounded; ENTIRE increment and signed multiplication retained. |

## Unpaid analytic residue

Writing A_t=(1-w^(32*L))*M_i/(2*Z1), G_t=I_i/(4*Z1) and
C_t=(k*rho/2)*OWNVar_i, the remaining sufficient estimate is JOINT control
of the sum of `A_t+eta_t*R_t+S_t-G_t-C_t`, for u<=t<2*u, against the SAME
filtered-start variance at lag u. No such useful comparison is supplied here.
Taking separate absolute bounds or dropping G_t and C_t loses the retained
cancellation. Fixed-member small drift/signed corrections do not supply a
changing-family variance-relative reserve. Scalar sign windows are not
physical trajectories; k, rho and eta retain parameter dependence.
Justified scaling, survival, physical mass, SAME OS/full QFT/continuum,
every group and Clay remain OPEN. Partial A03 only; exact canonical chart
claims are unchanged, so no ASCII or paper list is reprinted.

## Verification boundary

Accepted `/private/tmp/ym-chronological-exact-channel-cost-20261004-3.log`
exited 0, without warnings/errors, with SIX new public gates all within
{propext, Quot.sound}. Log SHA256:
`b0880c4613b1893f1ff9c488e6af6380398ae4410a0901144308bd871b9ac507`.
Frozen source SHA256:
`aef6bb2c5d105987a18cf5ad38e4e8b7750c4f7b274a94089a1046ad9aa4d546`.
The first two attempts failed on notation prechecking, omitted proof-only
section variables and a missing namespace open; they are REJECTED evidence.
No resource increase was needed. Each run used ONE monitored worker capped
at 20 GiB with 12 GiB reserve and fresh process/pressure/swap checks;
swap was zero. Independent semantic and backward analytic source reviews
found no center, partition or norm substitution. No new sorry/axiom/analytic
budget, weakened frontier, CI/resource change or chart closure. Root import
registration is NOT root verification; no full/root build, broad audit,
guard or metrics run. CI stays off.
