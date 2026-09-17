# Weighted cross terms and conditional control of actual terminal messages

Date: 2026-09-17 UTC. Base revision: `bbaab3e`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 for every
compact simple gauge group, with same-theory QFT structure and a positive
physical Hamiltonian gap, constructively within {propext, Quot.sound}. OPEN.

## A checked obstruction to an unqualified local-to-global step

`RationalWeightedProductGapObstruction` uses the fixed positive symmetric
stochastic kernel K=k tensor k, k=[[3/4,1/4],[1/4,3/4]], and the strictly
positive endpoint weight a=(9,1,1,9). State order is 00,01,10,11.
The actual weighted marginal is nu=a*(Ka)=(54,4,4,54), not counting measure.
Its total mass is 116. The observable f=(1,0,0,-1) has nu mean zero.
All these are evaluated definitions, not matrix-entry hypotheses.

With unnormalized forms N(r,s)=sum nu*r*s and
E(r,s)=one-half sum_xy a_x*K_xy*a_y*(r_x-r_y)*(s_x-s_y), the probe has
N(f,f)=108, mixed transfer pairing 81, and E(f,f)=27. Thus its Rayleigh
quotient is 1/4, below the one-factor lower/upper ratio 1/3.
`no_universal_singleFactor_gap` refutes preservation of that ratio under
arbitrary strictly positive endpoint weights, even for this fixed K.

The more informative calculation uses the ACTUAL coordinate averages:

    r_1 = P_1(a)*f - P_1(a*f) = (1, 9,-9,-1)/2,
    r_2 = P_2(a)*f - P_2(a*f) = (1,-9, 9,-1)/2.

Both satisfy P_i(a*r_i)=0, both also have zero nu mean in this witness,
and r_1+r_2=f. For D(r,s)=E(r,s)-(1/3)*N(r,s):

| Pair | N | E | D |
|---|---:|---:|---:|
| r_1,r_1 | 189 | 297/2 | 171/2 |
| r_2,r_2 | 189 | 297/2 | 171/2 |
| r_1,r_2 | -135 | -135 | -90 |
| f,f | 108 | 27 | -9 |

Thus individual sector bounds, explicit residual decomposition and even
marginal centering do not control the negative mixed defect. The missing
join is quantitative signed cross control, not merely existence of summands.

Exact source declarations:

- `kernel_positive`, `lean/YMGap/Continuum/RationalWeightedProductGapObstruction.lean:83`;
  `kernel_stochastic`, same file `:88`; `kernel_symmetric`, same file `:92`;
  `endpoint_positive`, same file `:97`; `marginal_endpoint`, same file `:106`.
- `mean_probe_zero`, `lean/YMGap/Continuum/RationalWeightedProductGapObstruction.lean:113`;
  `norm_probe` at `:115`, `cross_probe` at `:117`, and `energy_probe_quarter` at `:124`.
- `no_universal_singleFactor_gap`,
  `lean/YMGap/Continuum/RationalWeightedProductGapObstruction.lean:132`.
- `firstResidual_weighted_centered`,
  `lean/YMGap/Continuum/RationalWeightedProductGapObstruction.lean:164`;
  `secondResidual_weighted_centered` at `:169`, `residual_sum` at `:174`,
  `residuals_marginal_centered` at `:178`, and `residual_sector_bounds` at `:189`.
- `residual_mixed_energy`,
  `lean/YMGap/Continuum/RationalWeightedProductGapObstruction.lean:197`;
  `residual_gap_defects` at `:200` and `probe_gap_defect` at `:209`.

**Exact scope:** this finite model is NOT the actual Yang--Mills action.
The result refutes preserving its one-factor ratio 1/3, not every smaller
constant, the particular SU(2) headFloor/prefixCap value, or a separately
justified spatially uniform estimate for the actual terminal weight.

## Additional structure proved for the original terminal messages

For u_n=T^n1 with ORIGINAL T=K V, select an actual active coordinate i.
Write K=K_i*K_rest after a constructive finite permutation, and define

    r_i(y) = H_x[K_rest(x,y)*V(x)*u_n(x)].

`SU2QuaternionProductHeatConditionalMessage.productMap_conditional_pin`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatConditionalMessage.lean:60`)
uses conditional Haar self-adjointness, the original upper-factor marginal,
and independence of the erased output to identify P_i(u_(n+1)) with r_i
against every supported Haar test. This is NOT an asserted coefficient
identity for sphere heat normalization.

`productMap_floorCertificate` and `productMap_capCertificate`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatConditionalMessage.lean:139`
and `:162`) integrate the actual positive certificates (K_i-h)*K_rest*(V*u_n) and
(U-K_i)*K_rest*(V*u_n), giving h*r_i<=u_(n+1)<=U*r_i. Here h=headFloor(w)
and U=prefixCap(w). Every other kinetic factor and the entire original
spatial potential and terminal input are retained.

`BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage` constructs
this r_i on the actual carrier
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:58`).
Its `conditionalMessage_supported` at `:66`, `conditionalMessage_independent`
at `:71`, `conditionalMessage_pin` at `:91`,
`conditionalMessage_lowerCertificate` at `:103`, and
`conditionalMessage_capCertificate` at `:117` supply the support,
coordinate independence, conditional pin and both certificates.
The parameters width,n,K remain explicit, with 0<w<1 and K>=headCutoff(w).
The two constants depend on w, not width, n or K. The comparison concerns
u_(n+1), NOT V(y)*u_(n+1); the latter retains its output spatial potential.
No division, pointwise reciprocal, stationary vector or locality of the
terminal weight is asserted. Positive integrated mass is not silently
used as a pointwise lower bound.

These bounds provide original-message conditional normalization control.
They do not bound sensitivity to exterior coordinates or signed mixed
energy defects. No global contraction, OS limit or spacing estimate follows.

## The next actual analytic target

Keep the original polarized forms

    N_g(r,s) = m(g*Tg*r*s),
    E_g(r,s) = N_g(r,s) - m((g*r)*T(g*s)),
    B_g(r) = m(g*Tg*r),  Z = m(g*Tg),
    C_delta(r,s) = Z*E_g(r,s) - delta*(Z*N_g(r,s)-B_g(r)*B_g(s)).

The existing `local_sector_coercivity`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalDirichletCoercivity.lean:77`)
controls diagonal sectors. A global
join needs an actual weighted decomposition modulo constants AND control
of the signed off-diagonal C_delta terms, uniformly in the required width,
depth and late cutoff. Delta may need to be smaller than the local ratio.
This is the CLEARED covariance defect that the existing consumer needs;
it does not silently require the stronger raw-norm bound on every sector
sum, or assume that the present residuals have zero marginal mean.
No theorem supplying that control is asserted in this checkpoint.

The existing `weightedResidual_pairing`
(`lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:77`)
identifies conditional covariance
numerators, rather than declaring them zero. For a=Vg, the relevant test
for the mixed energy is (Tg)*s-T(g*s). For C_delta, retain the mean correction:

    Z*((1-delta)*(Tg)*s-T(g*s)) + delta*B_g(s)*(Tg).

Pairing this combined test with a*R_i gives the cleared covariance defect;
no reciprocal is needed. These identify the quantity to estimate; no new
assumption bundle or proof of its smallness has been added. Further work
must exploit the actual action/terminal structure, retain signed terms,
and track group and nome dependence. The universal endpoint-weight shortcut
is now excluded at its stated one-factor rate by the finite witness above.

The unchanged consumer is the all-observable same-odd-marginal estimate
`BF4ExactSlabFixedSpatialDirichletCoercivity.terminal_normalized_energy_variance_floor`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:284`).
Its currently supplied rate still collapses with width. Completed OS/scaling,
physical-time/mass calibration, nontrivial continuum survival, full QFT and
every compact simple gauge group remain OPEN. No canonical Clay atom closes.

## Verification

Four final focused checks pass through the monitored launcher, serialized
with one worker and the mandatory 20 GiB ceiling after fresh process/swap
preflights. Their 70 public axiom outputs (51 finite witness, 10 shared API,
3 generic conditional-message, 6 actual-message) are all within
{propext, Quot.sound}; final logs have no errors/warnings. Missing namespace
openings were repaired without changing statements or resource limits.
Independent mathematical source review covered the finite witness, generic
integrated certificates, actual terminal consumer and cleared-defect formula.
The cleared-defect discussion above is a mathematical target/derivation,
not a claim of a newly checked cross-defect estimate.

Five formerly private helpers in the shared one-factor module were exposed
with unchanged bodies/statements for reuse and included in its axiom check.
Root imports added; root/full-tree/full audit/guard NOT run. CI remains
manual-only. No sorry, new axiom, classical shortcut, old guard, canonical
frontier statement or safety limit changes. No canonical Clay atom closes.
No competing compiler/runner was observed; preflight swap decreased from
6781.19 MiB to 6677.00 MiB during the checks.

Final log paths and SHA-256:

- `/tmp/ym-weighted-product-gap-obstruction-20260917.log`:
  `06869e68f1fdb34cf08a072a2e1765a288ed391f5262e35107961b1f25831198`
- `/tmp/ym-local-gap-shared-api-20260917.log`:
  `4ee2f89ce90c4a5ae615337f695a0ccbb1218a07a267e2e9d134eddfed037452`
- `/tmp/ym-product-conditional-message-20260917.log`:
  `b10b5fc49bfd4c91d3c2f4d9aa096828f308f30c99ee3da9cdce875513eb1e40`
- `/tmp/ym-actual-conditional-message-20260917.log`:
  `dccd3d785692dcc1ed542b3cabeabcd4e2b761ebf8e95e04094c72277a9aa483`
