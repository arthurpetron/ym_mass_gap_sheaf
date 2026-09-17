# Local dual control in the original temporal marginal

Date: 2026-09-17 UTC. Base revision: `24928e9`.

Follow-up: `audits/AUDIT-TWO-LINK-SIGNED-DUAL.md` records the subsequently
proved two-link energy estimate and exact signed determinant split. The
finite-family budget, complete decomposition and global gap remain open;
the single-link result recorded here is unchanged.

Whole-project goal: for every compact simple G, construct nontrivial
continuum Yang--Mills on R^4 with same-theory QFT axioms, isolated vacuum
and positive finite physical Hamiltonian mass gap, within the project's
constructive {propext, Quot.sound} gate. This target remains OPEN.

## Proved increment

Write g=T^n1, a=Vg, t=Tg, nu=a*t, h=headFloor(w), U=prefixCap(w).
The new theorem, for supported f,q at an active link i, is

    P_i(nu*q)=0  =>  h*H[nu*f*q]^2 <= U*energy(g,f)*H[nu*q^2].

This is `actual_marginal_dual_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:274`.
The left and right pairings now use the ACTUAL marginal, not a*d_i.
The observable f remains arbitrary, and energy is the original temporal
Dirichlet energy, not a newly introduced heat-bath generator.

`marginalWeight` and `marginalPair`, same file:75 and :78, retain
V*T^n1*T^(n+1)1. The existing successor identity is `terminalMessage_next`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:57`.
The energy is `energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:63`.
Exact conditional centering is essential: H[nu*q]=0 alone is not the
hypothesis. `actualResidual_dual_energy`, new file:289, supplies concrete
tests q=P_i(nu)*s-P_i(nu*s) from supported s, using the existing
`weightedResidual` and `project_weightedResidual_zero`,
`lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:33` and :57.

## Causal proof and removed input

1. **Actual window, not an assumed inverse.** The original transfer and
   message certificates give ell=L/U and C=B/h+ell+1, where
   L=kineticFloor(w,width)*weightedMass(g),
   B=kineticCap(w,width)*weightedMass(g). The declarations `lower`,
   `upperBase`, `upper`, `lower_positive`, `lowerCertificate` and
   `upperCertificate` are in
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialErasedMessageWindow.lean:89`,
   :93, :97, :100, :129 and :149. They certify d_i-ell and C-d_i on
   the original carrier. The exact identities are

       d_i-ell = U^(-1)*[(U*d_i-t)+(t-L)],
       C-d_i   = h^(-1)*[(B-t)+(t-h*d_i)]+ell+1.

2. **Computed independent polynomial approximation.** `scale`, `radius`,
   `radius_nonnegative`, `radius_lt_one`, and `reciprocal` in
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialErasedMessageInverse.lean:131`,
   :145, :147, :150 and :177 construct alpha=1/C, rho=1-alpha*ell in
   [0,1), R=alpha*d_i-1, G_k=alpha*corrector(R,k). `reciprocal_independent`
   (:184) keeps the same erased coordinate; `reciprocal_cancellation`
   (:202) proves d_i*G_k+residual(R,k)=1. There is no exact polynomial
   inverse claim. `approximationCutoff` and `approximationInterval`
   (:229, :232) supply data for every positive rational tolerance and all
   later stages, including rho=0.

3. **Sharp corrected-multiplier square cap.** `residualCertificate` and
   `correctedSquareCertificate` in
   `lean/YMGap/Continuum/QuaternionHaarMonotoneGeometricInverse.lean:59`
   and :85 use a separate certificate of -R>=0. An interval alone does
   not supply this sign. With e=(-R)^k, 0<=e<=rho^k<=1 yields
   1-(1-e)^2=e*(2-e)>=0. The physical `multiplierSquareCertificate`
   and `multiplierErrorInterval`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialErasedMessageInverse.lean:209`
   and :218, control d_i*G_k, NOT G_k itself. No radius-1/2 restriction.

4. **Exact centering and one-U norm budget.** For r_k=t*q*G_k,
   `dualTest_centered`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:111`,
   proves P_i(a*r_k)=P_i(nu*q)*G_k=0 coefficientwise. Neither V nor t is
   declared independent. `dualTestNormCertificate` and
   `dualTest_norm_bound` (same file:127 and :164) use the positive defect

       U*a*t*q^2-a*d_i*(t*q*G_k)^2
         = a*d_i*t*(q*G_k)^2*(U*d_i-t)
           + U*a*t*q^2*(1-(d_i*G_k)^2).

   Positivity of a,d_i,t is constructed; q and G_k enter as squares.
   The existing erased dual estimate is `terminal_dual_energy`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDualDirichlet.lean:75`.
   Combining it with this norm budget gives `approximate_dual_energy`,
   new actual-marginal file:175, in the original energy of f.

5. **Remove all approximation losses.** `pairingErrorCap` and
   `dualTest_pairing_error`, new actual-marginal file:191 and :199,
   bound |H[a*d_i*f*r_k]-H[nu*f*q]| by rho^k times
   polynomialCap(f*q)*H[nu]. The private `geometric_square_closed`
   (:227) bounds the square error, selects an explicit rational geometric
   cutoff, and applies `Q'.le_of_le_add_mul_invSucc`,
   `lean/YMGap/Constructive/RegularCReal.lean:153`. No additional limit
   carrier, compactness or choice is needed. The resulting theorem removes
   every inverse cap, weighted mass, construction radius and presentation
   cap from the final coefficient.

This closes the previous checkpoint's reciprocal, centering, norm and
pairing-limit join to the actual marginal. It does not merely assume that join.

## Parameters and scope

The main theorem explicitly takes 0<w<1, every K>=headCutoff(w), arbitrary
width/depth n, an actual active link i, and supported f,q with the stated
conditional centering. The same f,q, weight and original temporal energy
remain fixed while the auxiliary polynomial degree k tends to infinity.

| Quantity | Definition | Dependence and role |
|---|---|---|
| h | `headFloor`, `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50` | Explicit w dependence; final local coefficient. |
| U | `prefixCap`, `lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:117` | Explicit w dependence; final local coefficient. |
| headCutoff(w) | `headCutoff`, `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55` | Explicit nome-dependent admissible-cutoff threshold. |
| ell,C | `lower`, `upper`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialErasedMessageWindow.lean:89`, :97 | w,K,width,n through original weighted mass and transfer floor/cap; construction only. |
| rho | `radius`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialErasedMessageInverse.lean:145` | Same construction dependence; strictly below one, not a proposed global spectral rate. |
| error amplitude | `pairingErrorCap`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:191` | Original marginal mass and observable presentation; removed in final inequality. |

There is no beta-independent positive margin or physical lattice-spacing
calibration in this theorem. It is an actual finite SU(2) estimate, not
an every-group theorem. Uniformity of its local coefficient in width/depth/
late cutoff is NOT a global spectral-gap conclusion. In particular, no
abelian exclusion or non-abelian mass-generation mechanism is established
by the positive-polynomial reciprocal argument.

## Next frontier, not a claimed consequence

The existing consumer is `clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
Its arbitrary-observable global energy/variance assertion still needs a
collective weighted decomposition and signed cross-energy budget. The local
dual estimate does not supply that input. Summing one copy per active link
incurs the number of links. Retain the SAME nu, original marginal-mean
correction and shared partition; no assumed residual orthogonality or
independent spatial/terminal weight is authorized by the new theorem.

The plan now prioritizes a concrete action-dependent estimate for those
remaining signed terms and its exact contribution to C_delta. Do not reopen
the proved reciprocal or completed-carrier construction to avoid this input.
The small-nome completed SU(2) gap remains preserved with its guards; its
incompatibility with the existing AF chart is unchanged. Spatial/scaling
control, same-theory QFT and Hamiltonian/time identification, positive finite
physical mass and every compact simple group remain OPEN. No canonical
frontier statement, guard or atom was changed or closed.

## Verification boundary

Four final focused Lean checks passed, serialized with the monitored
launcher, one worker and the mandatory 20 GiB ceiling. Fresh process/swap
preflights found no competing compiler/runner; swap remained 6669.00 MiB.
The modules print 7+7+13+10 axiom gates, all within {propext, Quot.sound}.
Final logs contain no errors, warnings or sorryAx. Initial parser, explicit
theorem-hypothesis, exponent-type and namespace repairs changed no claim.
Independent source reviewers checked both reciprocal construction and the
actual-weight norm/error/closure chain. No new sorry, axiom or classical
shortcut was introduced.

Four root imports were added. Root/full-tree/full-audit/guard checks were
NOT run; this is a focused verification claim only. CI remains manual-only.
No routine literature scan or resource-limit increase occurred.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-monotone-geometric-inverse-20260917.log` | `15d3efdfe7ab7413eceb9c6eeade55de9486ebecf561ec9d301c5a2617269dbc` |
| `ym-erased-message-window-20260917.log` | `69bb8dcef0727e0b71fbcfdcec50540f88682008f26e8ec22334650d14e2782a` |
| `ym-erased-message-inverse-20260917.log` | `636318393e9f0a730976432c1240ad26a65cab1e8673dce88c3ab8bb3f323f03` |
| `ym-actual-marginal-dual-20260917.log` | `9cb25591f976c124cacfc5c7ba433a30a9dc6aea0a25ce8d0ad49ebd610e0166` |
