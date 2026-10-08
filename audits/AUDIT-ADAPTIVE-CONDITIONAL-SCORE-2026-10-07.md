# Adaptive directions at the original conditional-score frontier

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms,
and a finite strictly positive physical Hamiltonian mass gap.

## Joint endpoint IBP screen: centered cancellation, no new estimate (2026-10-08 UTC)

Root source inspection and independent Sol mathematical review; the formula
below is a PAPER derivation using existing producers, not a new checked
declaration or signed relative bound. Selected experiment: combine the two
retained Ward responses before estimating either absolutely. Stop if the
result is exactly an already available correction rather than a smaller
analytic input.

Let V be the ORIGINAL spatial weight, a its actual terminal message,
g=V*a, A=T(a), b=T(a*phi), v the ORIGINAL spatial fringe mass, D=JA,
X=A(y)*phi(x)-b(y), N the matched noise, and
M=I_x[K*g*X*Jphi]. G is the actual successor polynomial reciprocal, not
an assumed exact inverse. All output factors are lifted to the second
endpoint. Write L=J_x+J_y, and H for joint Haar integration. The two retained
responses combine as

    U = density + 2*spatial
      = H[K*G(y)^2*D(y)*X^2 * L(g(x)*v(y)^2)]
      = -H[K*g(x)*v(y)^2 * L(G(y)^2*D(y)*X^2)].

The actual kinetic identity L(K)=0 is ALREADY supplied by
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularForm.lean:64`,
`productHeat_pairedAngular_carrier`, including every selected factor and
repeated index. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:118`,
`kineticWeight_eq_indexedProduct`, pins literal K. Signed joint IBP uses
`lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:120`,
`angular_pair_at`; both endpoint indices remain in range.

There IS a genuine centered cancellation: I_x[K*g*X]=0 removes the pure
output score term. Equivalently use LX=D*phi+A*Jphi-Jb directly;
I_x[K*g*X^2]=A*N and I_x[K*g*X*phi]=N. Expansion gives

    U = -H_y[v^2 * (
          A*G^2*N*J^2A + 2*G^2*N*D^2
          + 2*A*G*(JG)*D*N + 2*A*G^2*D*M)].

These are precisely the terms in the EXISTING combined Ward correction,
not a new sign-producing join. See
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:74`,
`ratioNoiseDensityMoment`, and private `hcorr:238` inside
`original_ratioNoise_ward_absorption_le:132`. In particular, centering
removes the pure score, but leaves the mixed gradient, reciprocal derivative
and marginal Hessian together; no useful sign or scaling smallness follows
from kinetic invariance alone.

The positive gradient pullback STILL has incoming weight
V*a*T(v*T(a)), not V*a*T(a) or V*a*T^2(a): same module `:384`,
`original_ratioNoise_gradientPayment_weighted_pin`. Constant/zero phi gives
X=N=U=0; constant a does not remove J(V*a). The finite closed-Wilson
vertex-gauge property in the parallel QFT audit is not this one-link paired
SO4 generator and does not supply a collective Gauss-Ward estimate.

Decision: PRUNE another joint-identity leaf; retain U as a combined signed
debt in the existing consumer. DIRECT original macroscopic response
retention or sufficient JOINT whole-window cost/OWN-variance control on a
justified changing family remains unpaid. Sharper local all-nome curvature
and its original-prefix transport are already available; do not rebuild
them or present a selected positive cap as a lower bound on actual signed
cost. No canonical field, source/action, frontier claim or chart changes.

## Direct retention need not pay the sufficient window test (2026-10-08 UTC)

Root calculation and independent mathematical review; NO Lean edits,
compiler run, new YM moment, analytic producer or canonical closure.
The user lattice-measurement note was already reconciled in
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; use its SAME-theory
correlation/clock distinction, not its fitted numerical mass as a premise.

Decision experiment: test whether a DIRECT macroscopic response floor can
be made to pass the factor-two signed-window budget using positivity alone.
The existing consumer is
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
`normalizedAnchorResponse_block_floor`; it accepts the direct ratio without
the budget in `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`. Reject any proposed mandatory budget join
if a strictly gapped vacuum-complement example separates the two. Budget:
hand algebra plus three tiny exact rational tests, no Haar expansion/build.

For EVERY integer u>=1 take lambda=1/100, mu=1-1/(4u),
T=diag(1,mu,lambda), vacuum=e0 and x=(0,lambda^u,mu^u). Its ordinary
Euclidean pairing gives

    R(n)=lambda^(2u)*mu^n + mu^(2u)*lambda^n,
    R(2u)=2*(lambda*mu)^(2u)>0,
    R(4u)/R(2u)=(mu^(2u)+lambda^(2u))/2 >= 1/4.

Here 0<lambda<mu<1: even the vacuum complement is strictly gapped at
each u. Bernoulli gives mu^(2u)>=1/2. With C the SAME response's even-lag
drop sum over t=u,...,2u-1, elementary geometric summation yields

    2*C/R(2u)
      = (1-mu^(2u))/(1+mu) + (1-lambda^(2u))/(1+lambda).

The first term is (1-mu)*sum_{j<u}mu^(2j), at least
u*(1-mu)*mu^(2u-2)>=1/8. The second is at least its first summand
1-lambda=99/100. Therefore the factor-two window reserve
1-2*C/R(2u)<=-23/200: it fails even kappa=0 while the direct macro
reserve is >=1/4. `computations/window_reserve_two_mode_screen.py` checks
these exact identities/bounds at u=1,8,64; finite Fraction assertions are
NOT kernel proofs. The all-u argument above is not newly formalized.
This is NOT a BF4 counterexample or continuum survival: indeed
R(2u)/R(0)<=2*lambda^(2u) tends to zero. No lower/upper physical-gap
claim for the original theory is inferred.

Endpoint-error review supplies no alternative analytic payment. Writing
delta_n=R(n)-R(n+1), mixed-moment telescoping gives
sum_{t=u}^{2u-1}m(2t,2)<=delta_(2u)-delta_(4u) and
2u*delta_(2u)<=R(0)-R(2u). The latter is a direct specialization of
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:71`,
`mixedMoment_time_budget`. An absolute same-source floor R(2u)>=eta*R(0)
would control that error, but
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedLogConvexity.lean:133`,
`macro_ratio_of_survival_floor`, already consumes the floor more directly.
Likewise the earlier SAME-source block floor is already consumed by
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:104`,
`response_shifted_block_step_lower`. Add neither endpoint wrapper nor an
unnecessary absolute-norm prerequisite to the normalized-anchor route.

Decision: retain DIRECT original macro moments as a co-primary analytic
producer; the signed-window sufficient estimate remains eligible, not
mandatory. Either route must still produce its actual original bound on a
justified changing family with its OWN centers and chronological masses.
Feasible exact-moment evaluation remains unpaid; the compression source map
is appended to `AUDIT-ORIGINAL-MOMENT-PILOT-FEASIBILITY-2026-09-30.md`.
No interface, hypothesis, frontier field or chart statement changes.

## Scalar/symmetric retention decision after the filter reduction (2026-10-08 UTC)

Root source inspection and two independent read-only mathematical screens.
This section supplies NO new interacting estimate or kernel-checked survival
theorem. The parallel boundary-list certificate is recorded in the QFT-inputs
audit; it does not pay the signed cost below.

For the OWN-centered symmetric origin sum S=chi01+chi02+chi12, existing
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`,
`familyExcitation_norm_floor`, gives R_S(0)>=3*varianceFloor(w) at fixed
strict nome and positive width. Its moments are not determined by the
antisymmetric x: source-level permutation algebra gives R_S(n)=3D_n+6O_n
and R_x(n)=2D_n-2O_n, where D/O are centered diagonal/off-diagonal face
responses. S keeps its moving OWN mean; do not impose the odd source's zero
mean on it. A sharper symmetric moment estimate remains NOT PRODUCED.

At padded width>=2, an ACTUAL existing Rayleigh floor is available:
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:104`,
`family_rayleigh_floor`, using
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:165`,
`familyResponseFraction`, and `:243`, `padded_family_energy_band`.
For three faces rho3=w^12*localLower(w,12)^2/localUpper(w,12)^2, with the
positive reciprocal explicitly constructed in that declaration. But
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:64`,
`familyResponseFraction_le_ceiling`, bounds THIS supplied floor by 2^(-840).
Its corresponding cost coefficient is therefore >=1-2^(-840), independent
of how close nome is to one. This is a limitation of the existing bound,
NOT a bound above on the actual Rayleigh quotient. Do not increase family
size merely to reuse this band. Width one is an actual fringe test:
`lean/YMGap/Continuum/BF4ExactSlabWidthOneGeometry.lean:75`,
`activeSpatialFaces_one`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:59`,
`inactive_face_time_one_zero`, kill each centered origin face. Bilinearity
therefore gives R_S(1)=0 for their sum (source-level consequence, NOT a new
symmetric-source theorem). This rules out that width, not padded sources.

The optional single filtered-slope seed
2*u*(R_x(2u)-R_x(2u+1))<=theta*R_x(2u), theta<1, would suffice for
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, by decreasing response drops. It is NOT
minimal or necessary. Exact scalar test, not a YM moment/eigenvector:
u=8, rho=7/8, R(n)=rho^n. Then the seed's left/right relative factor is 2,
but the aggregate window leaves positive margin

    (16*rho^16-1)/15 = 250251912402960/4222124650659840 > 0.

Thus a direct whole-window certificate can succeed where that convenient
one-slope prerequisite fails. Keep DIRECT aggregate/block retention as the
weaker main target; no new slope interface or stronger initial criterion.
Actual original finite ingredients remain
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:96`,
`originalOwnBlockVariance_pin`, and `:104`, `originalOwnBlockCost_pin`:
distinct Z0,Z1, moving OWN center and the COMPLETE signed cost. Neither
scalar-filter monotonicity nor a symmetric-source floor estimates these
quantities on a justified changing family. NEXT remains their original
interacting producer, not another source/symmetry/conditional wrapper.

## Selected independent-filter reduction and spatial-profile decision (2026-10-08 UTC)

Previous goal turn: PROGRESS, commit `81dbc973` supplies the actual common-
filter orbit identity. The remaining independent-filter branch is screened
by a stronger exact consequence, not by a new spectral or survival premise.

Write P(x)=orbitSum(x,cs), Q(x)=orbitSum(x,ds), for arbitrary finite signed
rational coefficients and natural time lags. On the EXISTING original
Wilson completion, strict nome and width>=1, select the proposition

    4*R_(P(x)+Q(y))(n) = R_(2P(x)-Q(x))(n) + 3*R_(Q(x))(n).

The SAME equality is sought for each forward lag difference R(n)-R(n+1).
Predicted outcome: the two-orientation finite Hankel/Krylov calculation
reduces to two scalar-filter responses of x; no additional orientation
overlap or independent temporal moment sequence is obtained. This does NOT
say scalar filtering cannot improve retention or produce a slow rate.
The elementary argument uses z=x+2y: every-lag B(x,T^n z)=0 and R_z=3R_x.
No norm inverse, nonzero filter, time-invariant local span or spectral
existence assertion is needed.

Inputs: `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:331`,
`mixed_response`, and `:340`, `diagonal_response`;
`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:166`, `orbitSum`,
and `:195`, `orbitSum_pairing`. The existing original-cost limits remain
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:130`,
`originalOwnBlockVariance_converges`, and `:143`,
`originalOwnBlockCost_converges`. Consumer: the actual filtered variational
screen, ultimately the signed relative budget at
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`. This reduction supplies no such budget.

Decisive tests: unequal filter lists and lags, arbitrary negative and zero
coefficients, empty filters, n=0 and width1 time-kernel components. Budget:
one bounded Sol leaf, independent final-source review, one serialized
20-GiB focused check with fresh dynamic preflight and 12-GiB host reserve.
Revise/stop if a new symmetry, analytic bound, carrier or spectral theorem
is required. Selection is not yet a kernel-checked result.

### Observed independent-filter proof (2026-10-08 UTC)

The selected response and cost-difference identities now PASS one final
focused Lean check; independent final complete-source mathematical review
passes. Arbitrary independent signed filter lists, repeated or empty lists,
zero/null directions, n=0 and width1 remain in scope. All objects are the
EXISTING original Wilson completion and its actual completed time.

| Produced result | Exact source |
| --- | --- |
| Every mixed lag of two independently filtered y directions equals its x counterpart | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:77`, `filtered_diagonal_response` |
| Signed mixed-filter response, with factor TWO cleared before the finite sums | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:89`, `filtered_mixed_response` |
| 4*R_(P(x)+Q(y))=R_(2P(x)-Q(x))+3*R_(Q(x)) at every lag | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:159`, `independent_filters_response` |
| Identical 4/1/3 decomposition of forward lag differences | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:210`, `independent_filters_forward_cost` |

Decision: reduce this two-orientation finite-filter search to the SAME
scalar moments R_x(n+i+j). Scalar filtering remains eligible and may change
retention; no useful moments, slow rate or overlap bound is produced here.
Different sites and the centered symmetric sector are NOT reduced to x.
The completed cost identity does not identify distinct finite chronological
partitions or authorize iterating a row-normalized finite transfer. Any
finite moment certificate must still retain its original window, OWN mean
and both masses; the radius-zero original-cost API is not asserted to be a
general finite mixed-filter realization. No new carrier/filter/interface,
variance inverse, nonzero premise or spectral theorem is introduced.

Verification: all four printed gates exactly {propext, Quot.sound}, no
sorryAx or warning in the final log. One serialized 20-GiB worker, 12-GiB
host reserve, fresh dynamic-capacity preflight before each launch. The first
check's one scalar-distribution rewrite error and its generated sorryAx
output are NOT evidence. The only repair distributes two explicit scales
using the existing RCscale_RCadd; no proposition or limit changed. Root
read the complete final source. Root import registered only; no root/tree
audit, guard, new hole/axiom, classical/native shortcut, canonical field or
chart closure. The whole Clay target and actual signed scaling input remain
OPEN. No broad discharge count is inferred.

Accepted log and SHA-256:

```text
/private/tmp/ym-origin-krylov-reduction-20261008b.log
  e4c5d82e78888236c1cfacf896691cbcb2b07a059ee653a787801dbb866961a0
```

Checked source SHA-256:

```text
81561d7aba782e486105a4f19f1cc82d75f4531bdf036469baa69498a73bfb49
```

### Spatial coefficient cancellation: source-backed screen, NOT a new proof

Root inspected the cited declarations; independent mathematical review
agrees. Actual rows use quaternion-tail correlations:

    Gamma_l(F) = 4*||sum_(p incident l) c_p*tau_lp||^2 - F_l^2.

Source: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:183`,
`actual_face_tail_recode`, and `:383`, `family_coherent_row`. The complete
original energy already retains these squares and BOTH Taylor debts in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`,
`family_coherent_energy_retained_square`. A scalar coefficient difference
does not identify the difference of these field-dependent ordered tails.

Exact paper test on actual adjacent words, not a new checked witness:
width>=2, shared link ((1,0,0,0),x1)=1; links ((0,0,0,0),x0)=i and
((1,0,0,0),x0)=-i; every other link=1. All values are rational unit
quaternions. With variable shared U, the two traces are chi(U*i)=-2U_i and
chi((-i)*U^-1)=-2U_i. At U=1, equal coefficients have shared angular square
16 and complete angular square 40, while opposite coefficients have shared
square 0 and complete square 24. Replacing -i by +i exchanges these cases.
Sources: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentAngularCancellation.lean:184`,
`original_adjacent_trace_pins`; and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:425`,
`adjacent_full_angular`. This rejects a universal PER-SHARED-ROW
coefficient-difference-only bound; it does not refute a global estimate with
separately paid true boundary rows or an estimate under the interacting law.
At this boundary row the incident spatial action remains
V_nonincident*h(-U_i)^2*h(U_0), h=the original heat prefix. The terminal
messages and all remaining action factors still belong to the original law.
No action or interacting moment is replaced by this pointwise paper test.

First-order source derivatives already cancel in
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:91`,
`sourceFirstOrder_eq_weightedAngularEnergy`; the higher signed terms remain.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`, retains 12*(1-w)*OWN variance plus the
complete signed correction, not an extra power from coefficient smoothness.
The concrete filtered target remains D<=epsilon*Z1*ell_V(b^2), with
D=Z0*E(A,phi)+boundaryDrift+signedMultiplicationCost and BOTH actual
chronological partitions. Its identity, not its estimate, is proved at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`,
`clearedRayleighCost_split`.

Decision: retain different sites and the centered symmetric sector as
genuine sources of NEW interacting moments; do not implement another
coefficient-gradient, Ward-cancellation or conditional matrix wrapper.
Work still requires an actual interacting correlation/signed-response
estimate and justified changing-family control. No broad chart claim closes.

## Selected actual three-face orbit response test (2026-10-08 UTC)

Proposition: on the EXISTING original Wilson completion at strict nome and
width>=1, set x=chi01-chi02 and y=chi02-chi12 for the three literal origin
spatial fundamental plaquettes. Prove, for every actual completed lag n,

    B(y,T^n y) = B(x,T^n x),
    2*B(x,T^n y) = -B(x,T^n x),
    B(a*x+b*y,T^n(a*x+b*y)) = (a^2-a*b+b^2)*B(x,T^n x).

Predicted consequence: no coefficient optimization in this TWO-dimensional
zero-sum origin-face orbit improves its normalized temporal response, including after
the SAME common actual time filter T^u. Independently filtered basis vectors,
other sites and higher spins are not excluded. The division-free identity covers degenerate/null
filtered directions; no norm inverse or transfer-invariance of this local
span is needed. This is an obstruction to a specific variational search,
not a bound on the response or a refutation of larger spatial profiles.

Available inputs: the actual U01/U12 pairing-preserving completed swaps and
their completed-time commutation, in
`lean/YMGap/Continuum/BF4WilsonAllNomeSpatialHeadSwapCompletion.lean:176`,
`completedSwap_time`, and `:231`, `completedInner_swap`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:70`,
`completedSwap_time`, and `:125`, `completedInner_swap`. Ordered reversed
face characters must be pinned by quaternion conjugation, not factor
commutation. Produce the literal source relations before using bilinearity:
U12*x=-x, U12*y=x+y, U01*x=x+y, U01*y=-y.

Consumer: the filtered Galerkin screen below. A matrix formed only from this
orbit with a common filter cannot produce a better chosen-source retention
via a maximum Ritz direction. Selected derivative/action insertions do not satisfy these pins
without transformation of their own indices and weights. Keep their full
signed costs; do not erase them by oddness.

Decisive tests: width0 excluded; width1/null directions permitted where the
stated type allows; arbitrary signed a,b, n=0 and changing coefficients;
all three literal ordered faces, physical x3 time and SAME normalization.
Budget: one bounded Sol leaf, independent complete-source review, root-only
20-GiB focused check after fresh dynamic preflight, 12-GiB OS reserve. Stop if
an assumed symmetry, new carrier or missing analytic input is required.
No new matrix interface or scaling hypothesis is selected. Observed results
will be recorded separately; this selection itself is not a checked proof.

### Observed original three-face response proof (2026-10-08 UTC)

The selected proposition is now kernel-checked on the actual original
completion; independent final complete-source mathematical review PASS.
Write R_x(n)=B(x,T^n x). All statements below name strict nome, width>=1,
and the existing physical completed time. No symmetry, analytic-smallness
or survival premise is supplied.

| Produced result | Exact source |
| --- | --- |
| Ordered source characters, including reversed faces by scalar conjugation | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:110`, `head_sourceCharacter`; `:119`, `axis_sourceCharacter` |
| Concrete face embeds transported on SAME completion | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:156`, `head_faceVector`; `:176`, `axis_faceVector` |
| Actual U12*x=-x, U12*y=x+y, U01*x=x+y, U01*y=-y | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:214`, `axis_x`; `:220`, `axis_y`; `:227`, `head_x`; `:234`, `head_y` |
| Literal x joins EXISTING antisymmetric source, including terminal zero-fold syntax | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:241`, `x_antisymmetric` |
| Every-lag 2*B(x,T^n y)=-R_x(n), R_y(n)=R_x(n) | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:331`, `mixed_response`; `:340`, `diagonal_response`; `:354`, `mixed_response_half` |
| Arbitrary signed rational a,b: R_(a*x+b*y)(n)=(a*a-a*b+b*b)*R_x(n) | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:400`, `trial_response` |
| SAME factor after COMMON T^u; cleared response-ratio equality, including null cases | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:413`, `common_time_filter_response`; `:435`, `common_time_filter_cleared_ratio` |

Decision: PRUNE coefficient-only optimization in this zero-sum origin-face
orbit under a common time filter as an improvement to normalized retention.
This does NOT show that the local span is time-invariant, produce a slow
rate, or exclude independent filters, other spatial sites, higher spins or
the centered symmetric combination. The common-filter assumption is
load-bearing. Selected derivative/action insertions still require their own
transformed indices and weights; oddness does not remove quadratic costs.
The NEXT estimate remains actual JOINT signed filtered cost/reserve versus
the SAME surviving interacting variance on a justified scaling family.

Verification: final focused check PASS, 29 printed gates (four axiom-free,
25 exactly {propext, Quot.sound}), no sorryAx or warning. One compiler,
20-GiB worker cap and 12-GiB host reserve, fresh capacity preflight before
each launch. The first two checks failed on bounded expression elaboration
and scalar syntax/distribution; their generated sorryAx output is NOT
evidence. Final repairs changed no proposition or premise and raised no
limits. Root read the final source; independent review passes. Root import
registered only; no full-root/tree build, guard, new hole/axiom, classical/
native shortcut, canonical field or chart change. The legacy progress metric
was not run because it invokes an unauthorized guard build.

Accepted log and SHA-256:

```text
/private/tmp/ym-origin-orbit-response-20261008c.log
  2f8a60bac4bc14f187b77b4897fa4d307229a1692369d0014371a338695de521
```

Checked source SHA-256:

```text
27bb668b2548a7105f89138dbd39ba08b3c244b7d963f41b6897108db6d2a785
```

## Curvature orientation and filtered variational screen (2026-10-08 UTC)

Root inspection and independent read-only mathematical review. These are
DERIVATIONS from existing declarations, not new kernel-checked estimates.
No hypothesis, compiler, source or canonical frontier is added by this screen.

### Regional log-concavity does not pay the required lower curvature

For X=relativeScalar, d=D_u X, R=sum(u_i^2), the actual frozen second jet
gives

    h*D_u^2 h - (D_u h)^2 = (h*h''-h'^2)*d^2 - R*X*h*h'.

Source: `lean/YMGap/Continuum/SU2QuaternionPairedFrozenJacobiCurvature.lean:54`,
`frozenHeat_second_pin`. Scalar log-concavity and h'>=0 would therefore
give an UPPER log-Hessian sign on X>=0. The actual certificate at `:83`,
`frozen_curvature_certificate`, instead gives

    C*R*h^2 + h*D_u^2 h - (D_u h)^2 >= 0,

a LOWER bound. The upper regional sign does not lower the required C.
It also says h*dd<=d^2, not that the integrated dd is nonpositive, as
required by `lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:148`,
`curvature_dual_bound`. The signed version `curvature_signed_dual_bound:180`
retains that term correctly.

The actual marginal expression retains A*D_u^2 A-(D_u A)^2+C*R*A^2:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalMarginalJets.lean:497`,
`localSignedFisher_marginal_pin`; the matched terminal consumer is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:649`,
`terminal_local_signed_score_bound`. Integrating a positive density adds
conditional score covariance to its log-Hessian. There is no produced
hemisphere restriction, southern-region payment or covariance bound here.
Moreover the Jacobi certificate is for the weighted approximant; the original
prefix lower-curvature transport does not assert a regional upper-sign pin.
**PRUNE a hemisphere-sign wrapper; it supplies no required payment.**

### Exact defect credit removes slack, not the missing rate

Write R(k)=B(x,T^k x), D=I-T, and m(k,l)=B(x,T^k D^l x). The existing
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:349`,
`mixedMoment_split`, gives the exact identity

    R(2*start)-R(2*(start+count))
      = 2*sum_{j<count} m(2*(start+j),1)
        - sum_{j<count} m(2*(start+j),2).

The retained second-defect sum is nonnegative by `mixedMoment_nonnegative:343`;
at even lag each summand is ||D*T^(start+j)x||^2. Thus the factor-two window
test in `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, is sufficient, not necessary. On a scalar
mode rho its credit is order (1-rho)^2 per step. At rho=1/4, start=count=1,
the actual macro retention is R(4)/R(2)=1/16, while twice the one-step cost
divided by R(2) is 3/2; the missing second-defect credit is 9/16. This is a
scalar test of sufficiency slack, not an original YM source or a scaling
counterexample. Fixed rho still loses every scale-independent macro floor
as the window grows. No estimate of this credit
against SAME filtered variance is supplied. A new exact-credit consumer alone
would just restate the macro-ratio obligation, so it is NOT implemented.

### A filtered Galerkin certificate is eligible, but must supply real moments

At one ORIGINAL chronological endpoint, use the literal moving OWN centers:

    v_i = T^u(g_stage*(f_i-c_i,stage))
    G_ij = ell(v_i*v_j)/Z0
    H_ij = ell(v_i*T(v_j))/Z1.

The six symmetric entries of a two-source compression can be represented
using `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:52`,
`observedMessage_endpoints`; `:88`, `block_window_numerator`; `:139`,
`normalized_block_window_pin`. The actual filtered norm/cost and their
fixed-source limits are pinned by
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:96`,
`originalOwnBlockVariance_pin`; `:104`, `originalOwnBlockCost_pin`;
`:130`, `originalOwnBlockVariance_converges`; `:143`,
`originalOwnBlockCost_converges`.

A genuine division-free sufficient certificate is the positive-semidefinite
matrix with entries

    Z0*ell(v_i*T(v_j)) - rho*Z1*ell(v_i*v_j).

It pays the chosen source only when its actual filtered numerator equals
sum(alpha_i*v_i). A maximum Ritz value alone gives a slow trial, NOT overlap
with the designated source. Rank one is precisely the missing filtered cost
estimate. A direct macro matrix B(v_i,T^(2u)v_j)-kappa*B(v_i,v_j) bypasses
the sufficient-only factor-two test, but its chosen-source quadratic bound
is the still-unpaid macro retention. Do not iterate (Z0/Z1)*T as if later
chronological partitions were unchanged. Zero/degenerate Gram directions
need no variance reciprocal.

The current family-band coefficients are already screened by
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:117`,
`family_band_coefficient_floor`, and `:139`,
`transported_family_band_coefficient_floor`; no duplicate ceiling is needed.
**Decision:** keep DIRECT filtered signed or variational control eligible,
but select no matrix interface without a concrete original-moment bound and,
where needed, quantitative source overlap. Neither this screen nor finite
spatial-symmetry work supplies survival or a scaling rate. Main work remains
the actual interacting producer, not more CS/completion/spectral wrappers.

## Remaining Gram-credit screen and route decision (2026-10-08 UTC)

Root source inspection and independent bounded mathematical reviews. The
following are algebraic DERIVATIONS from the cited declarations, not newly
kernel-checked theorems. They close no canonical proof node.

Keep the actual unfiltered source q, the literal antisymmetric f and the
full bare product heat P. Write

    lambda = w^12
    S = H[q*f^2*Pq]                 (original q*Pq marginal)
    E = S - H[q*f*P(q*f)]
    A = H[q^2*f^2]
    B = H[q^2*P(f^2)]
    C = singleEndedCost(q,f)
    I = sourceIncrementCost(q,f)
    V = 16*S - 8*E + Dplus
    X = H[W*jump(q)*jump(f)*sum(q)*sum(f)].

Both Gram means are already produced zero in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:214`,
`jump_mean_zero`, and `:226`, `sum_mean_zero`. The bare eigenpin is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`,
`spatialSpan_fullRange`; it is NOT an interacting-transfer eigenpin.

The scalar product of the two tests is jump(q^2)*jump(f^2). Applying
`lean/YMGap/Continuum/SU2QuaternionProductHeatJumpMean.lean:72`,
`jump_mean`, with squared inputs, and
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoungMoments.lean:92`,
`singleEndedCost_eq_moments`, gives

    X = 2*(A-B),
    C = 2*(1-lambda)*A - X/2.

`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoung.lean:203`,
`four_mul_sourceEnergy_add_increment_eq_two_singleEnded`, gives

    4*E + I = 2*C,
    I = 4*(1-lambda)*A - X - 4*E.

The denominator identity is
`lean/YMGap/Continuum/SU2QuaternionProductHeatSumNorm.lean:256`,
`sumTest_norm_energy_pin`. Consequently the checked budget at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:248`,
`original_energy_response_budget`,

    4*V*E + X^2 <= 2*V*C,

is exactly X^2<=V*I: Cauchy--Schwarz for the actual two tests. Cancellation
uses the displayed identity, not division by V or a source norm. It supplies
no new relative rate without a quantitative interacting-source estimate.

Decisive algebraic test: for q=1 and the centered bare eigenfunction,
A=B=S, X=I=Dplus=0, E=(1-lambda)*S, V=8*(1+lambda)*S. The budget saturates.
For the zero source every displayed quantity is zero. These are tests of
the generic inference, NOT actual BF4 terminal-source instances or a
Yang--Mills counterexample. The actual q retains spatial action and terminal
messages. In particular A uses q^2 while S uses q*Pq; they are not identified.

The one-face square image already exists at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:77`,
`square_heat_moment`. It still retains an unrestricted signed q^2-weighted
spin-two moment. A shared-link image for the two-face square would compress
X into further loop moments, not estimate their sign or size. No such image
is implemented here solely to replace the missing estimate by another list.

**Decision: REVISE the Gram branch to an interacting producer, not another
CS/square-moment wrapper.** The next required output is the JOINT signed
filtered cost versus its SAME surviving variance, or an actual original
blocking comparison that produces it. The existing consumers are
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, and the actual profile identification in
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:130`,
`originalOwnBlockVariance_converges`, and `:143`,
`originalOwnBlockCost_converges`. Direct filtered control remains eligible;
the stronger initial unfiltered Rayleigh floor is not imposed as necessary.

### Even-cost and original time-decimation checks

Antisymmetry reverses b=T^t(g*f), u=A*f and b-u. Both factors of
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:144`,
`signedMultiplicationCost`, reverse, so their pairing is EVEN. Energy,
surviving variance and `boundaryDrift:136` are even as well. No useful
quadratic sign follows from the zero means. The actual source is not
energy-null: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`,
`family_energy_floor`, with coefficient budget 2, gives
2*lower(w)<=600*upper(w)*normalizedEnergy. This is a finite energy lower
bound, not an upper estimate on filtered cost.

At arbitrary cutoff, original time-decimation gives

    L2(x,z) = integral K(x,y)*V(y)*K(y,z) dy,
    endpoint law = V(x)*L2(x,z)*V(z)/Z2.

Exact source: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:61`,
`middleIntegrand`; `:73`, `gluedMiddle`; `:188`, `original_twoLayer_gluing`.
Its compression is the actual polynomial at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoundaryCarrier.lean:173`,
`kernel`, with reconstruction `kernel_reconstructs:182`. Middle V occurs
once; neither endpoint V is erased. The bare L2 row is T1, not an asserted
unit row, by `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGluedEndpointMarginal.lean:105`,
`chronological_middle_pairing`, and `glued_lower_endpoint_pairing:169`.
Including the upper V yields row T^2(1), with the original partition at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:102`,
`chain_partition_pairing`.

Where the positive conditional ratios are defined, let g_d=T^d(1).
The two-step row normalization would be P2(f)=T^2(f)/g_2. Its repetition
inserts T^2(T^2(f)/g_2)/g_2, NOT the chronological four-step ratio T^4(f)/g_4
without an additional identity. In a longer unchanged original chain the
endpoint law instead retains V(x)*g_d(x)*L2(x,z)*V(z)*g_e(z)/Z_(d+e+2);
its forward conditional is T^2(g_e*f)/g_(e+2). These are derived normalized
expressions, not new polynomial operators or checked stationarity claims.
Original iteration and exterior-message pins:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalIteration.lean:182`,
`original_chain_iteration`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:63`,
`terminalPair_total`.

The existing actual conditional projection is on ORDINARY weighted state
GNS: `lean/YMGap/Continuum/BF4ExactSlabBlockConditionalProjection.lean:90`,
`conditionalProjection`; `:158`, `conditionalProjection_norm`. A theorem
identifying it with a map on the all-nome reflected OS carrier is NOT FOUND
in that module or the cited original gluing/marginal modules. Do not infer
an OS gap or the relative RG comparison from its norm-one bound.
Non-strict same-carrier time contraction is already available at
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:191`,
`completedInner_time_contraction`; it supplies no useful new scaling margin.

No compiler was used for these screens. No new hypothesis, stationarity
premise, canonical field, continuum claim or chart change is introduced.

## Selected antisymmetric ORIGINAL source (2026-10-08 UTC)

Proposition: for width>=1 take the literal fundamental-character difference
between origin faces p01 and p02, with coefficients +1,-1. The existing x1/x2
swap exchanges these ordered loops without reversal. Prove its finite
original chronological scalar, endpoint means and moving OWN center are
exactly rationally equivalent to zero, at every stage/depth, and exhibit
its nonzero state on the EXISTING completion with the existing two-face
variance floor. Do not merely assume an odd source or a symmetry witness.

Inputs: `SpatialAxisSwapWilsonWindow.originalWindowScalar_swap`, literal
physical plaquette loops, original finite linearity and endpoint pins,
`PlaquetteFamilySourcePin.familyExpression`, and
`PlaquetteFamilyVariance.familyExcitation_norm_floor`. Consumer: specialize
the new SAME-source OriginalRayleighLimit without moving-center debt, and
remove the completed mean-product correction for this produced source.
This is a selected-source algebraic simplification, not a slow-rate estimate.

Independent source screens predict success. Decisive tests: exclude width0,
check physical nonrepeated faces, keep all action/partition factors and source
inverse flags, and retain coefficient-square budget 2. The quadratic signed
costs are swap-even and do NOT vanish. Unrelated Gram-test means require their
own invariant-weight pin; do not erase them from odd marginal mean alone.
Budget: bounded Sol finite-source implementation, root completed/variance
consumer, independent complete-source review, serialized root-only focused
20-GiB checks with 12-GiB reserve and fresh dynamic-capacity preflight.
Stop if an existing identical producer is found or an additional analytic
premise is needed. No new norm inverse, completion, scaling input or canonical
field change is selected. Observed proof evidence is recorded separately.

Bounded follow-on decision: the actual Gram means J and M can be tested
without a new transfer-symmetry framework. The existing product-heat jump
and sum-test mean pins reduce them to H[q*f] and H[q*P(f)]. For this literal
two-face family the existing full-range heat eigenidentity gives P(f)=w^12*f.
Use the original zero mean at L=0,m=depth,n=0 and its positive chronological
partition to prove H[q*f]=0, retaining q as the projected ORIGINAL terminal
source. Strict padding from spatialFaces(1) requires width>=2 to supply
the existing fringe-independence guard; width1 nondegeneracy is not survival.
Predicted output: J=M=0 in the actual SourceVarianceGram consumer, with
the swap-even cross credit and source-jump square UNESTIMATED. Budget: one
bounded Sol leaf, root-only capped check, independent full-source review.
Stop rather than assume q invariance or replace its weight/action. This
removes actual mean corrections, not a signed scaling obligation.

### Observed antisymmetric-source proof evidence (2026-10-08 UTC)

All three selected leaves now pass focused kernel checks. Independent
complete-source mathematical reviews pass; final compiler fixes changed
only imports, namespace/notation resolution, explicit sequence annotation
and local unfolding, not any statement or premise.

| Produced result | Exact source |
| --- | --- |
| Physical distinct p01,p02, literal ordered loop exchange and coefficient-square budget 2 | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricPlaquette.lean:50`, `face01`; `:51`, `face02`; `:57`, `faces_physical`; `:69`, `coefficient_square_budget`; `:87`, `swapSourceLoop_face01` |
| Every finite ORIGINAL chronological mean is zero | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricPlaquette.lean:126`, `original_mean_zero` |
| Exact endpoint and moving OWN mean zero, literal centered source unchanged | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricPlaquette.lean:168`, `endpointMean_zero`; `:176`, `ownMean_zero`; `:191`, `shifted_source_pin` |
| Existing joint-limit/unit pairing zero; centered moments equal raw moments | `lean/YMGap/Continuum/BF4WilsonAllNomeAntisymmetricPlaquette.lean:60`, `joint_mean_zero`; `:72`, `state_mean_zero`; `:85`, `centeredMoment_uncentered` |
| Raw embed in SAME vacuum complement, squared norm >=2*varianceFloor(w)>0, SAME completed time correlator | `lean/YMGap/Continuum/BF4WilsonAllNomeAntisymmetricPlaquette.lean:100`, `excitation`; `:128`, `excitation_norm_floor`; `:136`, `excitation_norm_ne_zero`; `:159`, `excitation_correlator_pin` |
| Literal spatialSpan recoding and PRODUCED fringe independence for width>=2 | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:82`, `source_spatialSpan_pin`; `:87`, `source_fringe_independent` |
| Actual OWN-centered span is coefficient-pinned to original Wilson source | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:135`, `ownMean_spatialSpan_pin`; `:141`, `oddCentered_source_pin` |
| Separate one-sided raw mean H[V*g_depth*f]=0, then actual projected H[q*f]=0 | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:162`, `raw_endpoint_mean_zero`; `:188`, `projected_endpoint_mean_zero` |
| Both actual Gram means J=M=0 and simplified original energy budget | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:203`, `projected_heat_mean_zero`; `:214`, `jump_mean_zero`; `:226`, `sum_mean_zero`; `:248`, `original_energy_response_budget` |

Interpretation: width>=1 gives a nonzero exactly centered initial source;
width>=2 supplies the stronger fringe guard needed by the finite energy
consumer. The one-sided terminal mean is proved independently of the OWN
odd-marginal mean: no substitution between these two densities occurs.
The bare P(f)=w^12*f pin is used ONLY under the actual q insertion to remove
linear means. No interacting-transfer eigenvalue is inferred. The final
finite budget retains V=16*S-8*E+Dplus and X=H[W*r*s], giving
4*V*E+X^2<=2*V*singleEndedCost. Neither Dplus nor X is estimated here.
The source/nome/width stay fixed in the limit. No positive-time lower bound,
changing-family modulus, scaling-uniform floor or physical/Clay closure.

Verification: three successful serialized focused checks, 15+11+10=36
printed gates, each empty or within {propext, Quot.sound}, no sorryAx.
One compiler, 20-GiB cap and 12-GiB OS reserve, with fresh dynamic-capacity
preflight before each launch; swap use remained zero. The Gram check has
one harmless unused-section-variable warning on the private q_supported
helper. No full-tree/root audit or regression on unchanged machinery.
Root imports are registered only. No new hole/axiom, classical/native
shortcut, option-limit increase, canonical field or chart change.

Successful logs and SHA-256:

```text
/private/tmp/ym-antisymmetric-finite-20261008b.log
  92b0f4a746445c5ff53e5e1d54c0c96a7a51575e036a11b08390c721f83af92d
/private/tmp/ym-antisymmetric-completed-20261008b.log
  bd758ada980f2f220989df46a3e0e80d875fc7331efb78c1b41e7a0a60b21227
/private/tmp/ym-antisymmetric-gram-20261008c.log
  46d67c47ed818e00497c846f98e216968aeada609757874dcb7299c3fb265ac2
```

Checked source SHA-256, in the same finite/completed/Gram order:

```text
d1ba1be8ee93082fd970158991acded74438c727b2cb20669ec53a9cf1e6e189
715a12ec41c5b794fa90703fa6abdd324375fda650cc6bcce71269f1157d8098
21bd34812ce33fcc7dac5ec83961428969955b72b7de09ee33f9178a5afdc6be
```

Decision: CONTINUE to the actual signed relative cost/reserve, not another
mean or completion wrapper. This source removes centering terms, but a
filtered proof must still control its SAME surviving filtered variance.
The stronger optional initial-energy condition is not imposed as necessary.
An independently reviewed algebraic lead, NOT a new checked declaration:
after the center pin, r*s=jump(q^2)*jump(f^2). The existing
`lean/YMGap/Continuum/SU2QuaternionProductHeatJumpMean.lean:72`, `jump_mean`,
then yields X=2*(H[q^2*f^2]-H[q^2*P(f^2)]). This preserves the signed
quadratic response and supplies no sign or useful relative estimate.
The existing full angular/Ward/Taylor costs cannot be erased by oddness.

The latest user's lattice-measurement attachment matches the cached
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` review exactly. Retain its
channel-versus-every-state and physical-time calibration distinctions;
do not refetch papers or import fitted masses as constructive premises.

## Bounded loop-moment compression screen (2026-10-08 UTC)

Targeted primary-source research alongside the finite spatial-symmetry check;
not a routine arXiv listing scan and not a new proved scaling estimate.
Kazakov--Zheng's finite-N bootstrap uses SU(2) trace identities to close
Wilson-action loop equations on single traces. Its sections 3 and 4.2 use
Hermitian/reflection positive moment matrices and a Schwinger--Dyson-generated
finite hierarchy. Section 4.3 reports plaquette bounds and qualitative string
tension estimates; section 5 retains the local-region/large-loop bottleneck
and does not supply our scaling survival theorem. The action in equation (20)
is the exponential Wilson action, not the current finite heat-prefix action.
Do not import its loop equations unchanged.
[Primary paper, equations (1), (20), (76), sections 4.3 and 5](https://arxiv.org/html/2404.16925v2).

Root inspection and a bounded Sol read-only review locate existing original
constraints. `lean/YMGap/Continuum/BF4ExactSlabLocalHaarWard.lean:51`,
`fullAction_pair_pin`, retains every incident AND complementary heat factor;
`fullAction_local_ward:85` gives H[R*((DA)*f+A*(Df))]=0 with proved DR=0.
`fullAction_score_identity:106` is already present. There is no reason to
build that Ward interface again. From the literal `PolyQuaternion.conj:130`
and `PolyQuaternion.mul:138` in
`lean/YMGap/Continuum/BF4GeometricSpinNetworkMehler.lean`, scalar-component
algebra gives 2*sc(U)*sc(V)=sc(UV)+sc(U*conj(V)). This is a DERIVATION, not
a newly checked named trace-reduction declaration. Interpreting both terms
as actual source loops also requires compatible basepoints; conjugate is
inverse only with the unit relation. Full-action dependence cannot be
discarded under an independent-tail fusion hypothesis.

Critical normalization test: write S=ell(b*b), J=ell(b*T(b)). The existing
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`,
`clearedRayleighCost`, gives C=Z1*S-Z0*J. The actual definitions
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:84`,
`originalOwnBlockVariance`, and `originalOwnBlockCost:89` give v=S/Z0,
e=C/(Z0*Z1). Algebraically, Z0*Z1*(c*v-e)=(c-1)*Z1*S+Z0*J.
Thus the normalized comparison is not an affine objective in unspecified
moments of ONE marginal: both chronological masses and OWN center must be
certified. Each lag retains its own Z0,Z1. A single stationary Wilson-action
moment matrix does not identify them or the current full heat transfer.

Decision: retain loop/SOS compression as an unimplemented candidate for an
exact finite certificate, only after its actual source basis, SAME-law Ward/
positivity constraints, normalization and omitted-mode error are supplied.
Rust may propose rational data; Lean must independently check it. Do not
launch an SDP, add a conditional certificate framework, or impose separate
per-lag positivity as a necessary condition for the signed aggregate.
The consumer is still `WindowSignedCost.aggregate_window_macro_ratio:181`
in `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean`; its complete
joint relative budget remains OPEN. No new mathematical proof or chart
closure results from this research screen.

## Full-cost and filtered-reserve screen (2026-10-08 UTC)

Root source inspection and two independent bounded read-only reviews; these
are mathematical DERIVATIONS, NOT newly kernel-checked declarations. No
compiler run, Lean edit, literature fetch or canonical proof-node closure.
The repeated lattice-measurement attachment is already covered by the
corrections in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.

**Shared-link branch.** The proposed certified-W inequality
H[W Gamma_shared(a*f+b*g)] <= 8*a^2 H[W(2-d)]+8*(a-b)^2 H[W] is valid,
but it supplies no new cancellation or smallness. For the actual neighboring
faces at width>=2, the existing FULL arbitrary-signed identity at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:425`,
`adjacent_full_angular`, with `cross_local:266` and `shared_squares:357`, gives

    Gamma_full(a*f+b*g)
      = 3*a^2*(4-f^2)+3*b^2*(4-g^2)+Gamma_shared(a*f+b*g).

Thus shared-link cancellation leaves THREE nonshared contributions per face.
Under the SAME certified W they are nonnegative, not uniformly strictly
positive: zero W/coefficients and small weighted deficits remain allowed.
`adjacent_full_angular_paid:451` already retains the equal-weight difference
square. The whole-family version already reaches the COMPLETE original
channel energy, with BOTH Taylor debts, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`,
`family_coherent_energy_retained_square` (full angular identity at :163,
`family_coherent_full_angular`). PRUNE implementing the redundant shared-block
8/8 estimate. This does not rule out a useful whole-profile interacting bound.

**Filtering branch.** The consumer remains
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, with finite square specialization
`original_window_budget_macro_ratio:245`. For a scalar eigenmode T*x=rho*x,
0<rho<1, x nonzero, R(n)=||x||^2*rho^n gives

    2*sum_{j<u}(R(2*u+2*j)-R(2*u+2*j+1))/R(2*u)
      = 2*(1-rho^(2*u))/(1+rho).

This exceeds one when rho^(2*u)<(1-rho)/2. A finite polynomial or Cesaro
filter either kills this eigenvector or only multiplies it; its surviving
relative cost does not improve. This screens a generic inference, NOT an
exhibited YM eigenvector or an actual YM-source counterexample.
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:122`,
`timeDefect_bound`, pays absolute decay against the PREIMAGE norm.
`lean/YMGap/Continuum/BF4WilsonAllNomeMacroRatioFilteredCost.lean:100`,
`retained_time_budget`, retains the earlier response; `macro_to_filtered_budget:123`
requires the missing macro survival ratio. Conversely,
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:102`,
`response_step_lower`, and `response_geometric_lower:117` propagate a supplied
selected-source Rayleigh floor, but do not produce a sufficiently slow rate.
NEXT is that ORIGINAL interacting source-specific reserve, or quantitative
slow-mode overlap, not another absolute-smoothing/completion wrapper. Keep
complete signed cost and SAME filtered OWN variance; a DIRECT filtered proof
remains eligible without a stronger unfiltered initial floor.

**Optional unfiltered profile route.** Bare full heat acts by w^12 on every
signed profile (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`,
`spatialSpan_fullRange`), independent of coefficient smoothness. This is NOT
an interacting-transfer eigenvalue. The original interacting identity is
E=12*(1-w)*V+R at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`; R is the COMPLETE signed `varianceRemainder:42`.
Put s=side(j), delta=afGap(j)=1-afNomeSchedule.nome(j), V>=0. If s*E<=c*V
and c<=6*s*delta, rearrangement gives R<=-6*delta*V, without inverting V.
The second condition holds after the computed
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:84`,
`afPowerBudgetCutoff`, with p=1, cap=c/6, by `afPowerBudget_gt:100`.
The schedule pin is
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:274`, `afNomeSchedule`.
This locates the needed negative leading-order response, but produces no bound
on R, energy lower bound or physical calibration. Do NOT apply Casimir 12 to
filtered b/A or make this optional stronger criterion necessary for that route.

Decision: retain the complete signed interacting estimate as the producer;
neither local coefficient smoothing nor generic time filtering replaces it.
No useful scaling budget or continuum survival is proved by this screen.
Whole Clay target remains OPEN; no chart reprint.

## Selected SAME-source filtered-profile join (2026-10-08 UTC)

Proposition: for any ORIGINAL radius-zero Wilson expression e, let
f=sourcePolynomial(e), K=headCutoff(w)+stage, c_stage its actual odd mean,
A=g_(stage+t), b=T^t(g_stage*(f-c_stage)). Prove that ell(b^2)/Z0 converges
to the EXISTING centeredTimeMoment(2t,state(e),state(e)); prove that the
literal clearedRayleighCost(A,b)/(Z0*Z1) converges to that moment minus the
moment at 2t+1. Z0=ell(A^2) and Z1=ell(A*T(A)) remain distinct. No inverse
norm, new action, completion or analytic smallness premise is needed.

Consumer: the actual filtered signed-profile cost in the generic completed
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`. The published finite original window
specialization is still square-specific at `original_window_budget_macro_ratio:245`.
This selected increment constructs the finite numerator/denominator join,
not another conditional macro-ratio theorem or the analytic window budget.

Available inputs: arbitrary supported finite pins
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:140`,
`normalized_block_window_pin`, and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighWindow.lean:89`,
`clearedRayleighCost_window_pin`; the already generic completed pairing
`lean/YMGap/Continuum/BF4WilsonAllNomeZeroRadiusIncrement.lean:168`,
`time_pairing_lag`. Independent duplicate screening found that moving OWN
center convergence is still loop-specific. The old loop API must be retained;
extend it minimally and expose the computed mean threshold as data.

Reason for selecting this join: the actual family's Casimir-12 identity
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`, concerns the unfiltered spatialSpan.
It cannot simply be applied to the later filtered ratio b/A. Direct filtered
analysis must use the actual block cost/variance, not substitute a different
endpoint variance. Stop if a generic moving-center diagonal limit already
exists, a new analytic premise is needed, or old public statements change.

Predicted outcome: the fixed-member join is constructible from existing
original mixing/mean control. Mean cutoffs must be named computed data;
all limits fix w, width, e and t. Empty/constant/zero sources remain allowed;
no positive norm or changing-family conclusion is inferred. Budget: bounded
Sol implementation in two files, independent complete-source review, root
sole focused monitored checks with fresh memory/swap preflight, one worker,
20-GiB ceiling and 12-GiB reserve. No full-tree build/audit or chart closure.
Results are recorded separately below after verification.

### Observed source join and next mathematical decision

The selected fixed-member join is now kernel-checked:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:104`,
  `expressionRaw_original_pin`, transports the complete source polynomial
  through its actual padded chronological window. At :128,
  `expressionCenteredTimeMoment_chronological_pin` identifies the EXISTING
  completed centered moment, not a replacement functional.
- The named computed cutoff at :158, `expressionEndpointMeanThreshold`,
  combines the original singleton joint modulus with a geometric cutoff.
  `expressionEndpointMean_approx:164` gives both approximation inequalities;
  `expressionOwnMean_converges:225` retains the actual odd-window mean.
  `expressionOwn_centeredPair_converges:251` expands this moving center
  before taking the fixed-expression limit.
- `lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:84`,
  `originalOwnBlockVariance`, and :89, `originalOwnBlockCost`, construct
  exactly the quantities selected above. Their finite pins are
  `originalOwnBlockVariance_pin:96` and `originalOwnBlockCost_pin:104`.
  `originalOwnBlockVariance_converges:130` and
  `originalOwnBlockCost_converges:143` give precisely the SAME lag-2t
  centered moment and its lag-(2t+1) difference. Only positive chronological
  vacuum partitions are inverted; no observable norm is inverted.
- The three old single-loop APIs at OwnCenterLimit :305/:314/:323 remain
  specializations. The unchanged
  `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean`
  also passes a focused consumer regression against the generalized API.

Independent complete-source review passes, including the final technical
repairs. Root alone ran the serialized checks, each with one worker,
a hard 20-GiB ceiling, 12-GiB reserve and fresh process/memory/swap preflight:

| Final focused check | Log | Printed axiom gates |
| --- | --- | --- |
| WilsonOwnCenterLimit | `/private/tmp/ym-expression-own-center-20261008d.log` | 12, all exactly `{propext, Quot.sound}` |
| OriginalRayleighLimit | `/private/tmp/ym-expression-original-rayleigh-20261008b.log` | 6, all exactly `{propext, Quot.sound}` |
| unchanged square consumer | `/private/tmp/ym-expression-square-regression-20261008a.log` | 4, all exactly `{propext, Quot.sound}` |

Initial checks caught omitted proof-only section binders, doc/include order,
opaque raw-pair elaboration and an implicit convergence sequence. Those
were repaired without mathematical statement changes. Failed-check
`sorryAx` output is NOT proof evidence; every final gate is clean.
Source SHA-256 values, in the same order as the table:

```
79d5aeb211903d306396430a2f0c16a81d2b58e2ebc9abb9622d6c0d763d79f7
ec1ad9e7fd2dd28bf2cce0655686b2fd8497a922a99b401bf224614ac9229c5c
cc4e387b51929dfd2e29cdc408cd1fcb8d70fae38bf1b8444973090ca9cb0957
```

Decision: continue the JOINT signed-profile cost estimate against this
SAME filtered variance. No more source/limit wrapper is needed for a fixed
radius-zero member. The existing literal split at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244`,
`original_block_rayleigh_split`, retains energy, terminal drift and signed
multiplication cost together. Its :283, `terminal_clearedRayleighCost_le`,
pays the boundary term but leaves the energy and signed commutator unpaid.
The initial-source `FamilyMarginPencil.pencil_contract:278` is not a
filtered-cost estimate. None of these facts justifies substituting the bare
family Casimir identity for the later ratio b/A.

No new analytic premise, hole, axiom, proof limit, canonical field or broad
chart status changed. Nome, spatial width, expression and lag remain FIXED;
changing-family/spacing control, macro survival, nontrivial continuum,
physical mass, QFT axioms and every-group Clay closure remain OPEN.
The root import is registered only; no root/tree build or audit was run.
The user's lattice-measurement note remains incorporated with the primary
source corrections in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`;
no measured mass, finite-spacing Hamiltonian identification or area-law
inference is imported as an analytic premise.

### Parallel source screening retained in this decision

No adaptive-order interacting remainder producer was found in the inspected
source. The strongest relevant produced source error is cubic Sobolev plus
the omitted heat tail:
`lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:89`,
`sourceError_le_sobolev`. It retains actual derivatives of q, q*f and q*f^2,
q=projectedEndpointSource(V*g_depth), not just bare family degree 12.
`completeRemainder_le_sobolev_completedSquare:138` already retains the
negative commutator square; do not rebuild that cancellation.

Global sum(c_p)=0 does not remove the quadratic Ward matrix. From
`lean/YMGap/Continuum/SU2QuaternionWeightedCasimirWard.lean:45`,
`blockResidual`, the residual of F=sum c_p*f_p is a sum of
c_p*c_q*H[(f_p-mu_p)*(JW)*(Jf_q)]. Even granting equal means, coefficients
(1,-1) leave W_pp+W_qq-W_pq-W_qp. The existing coherent row sum only uses
incident faces (`FamilyCoherentTail.aggregateCoherentTail:92`); disjoint
opposite coefficients do not cancel singleton link rows. No new zero-sum
or summation-by-parts smallness premise is adopted.

No produced blocking estimate fills the AF original filtered budget:
`lean/YMGap/Continuum/CompactDualCutoffOnePhysicalPushforward.lean:290`,
`physicalRemainderL1_le_two`, is only a cutoff-one cap of TWO;
`lean/YMGap/Continuum/Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge.lean:371`,
`centeredCylinderRemainder_abs_le_of_balanced_and_margin`, explicitly takes
the missing balanced and margin estimates. The scale-five fusion prefix
does not produce the original action/fusion-power pins. These are dated
source checks, not fresh compilation or a nonperturbative error bound.

## Selected fixed-power AF payment test (2026-10-08 UTC)

The spatial-profile screen has a real microscopic degree advantage: the
existing `FamilyHeatEigen.spatialSpan_fullRange` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`
has factor w^12 independent of family size, unlike the growing square.
However `AFPaddedTrajectory.afBareHeatLoss_no_uniform_cap` at
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:451` already
rules out deriving uniform rescaled H1 from that factor alone. The actual
`FamilyVarianceTaylor.padded_family_energy_variance` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`
retains 12*(1-w)*OWN variance PLUS the unpaid signed remainder.

Next mathematical test: on the ACTUAL afGap(j), construct an all-tail
cutoff for C < side(j)*afGap(j)^p, for EVERY fixed natural p and rational C.
The linear denominator bound gives 3*(j+1)*afGap(j)>=1; the existing
`PolynomialGeometricDecay.polynomial_bound` at
`lean/YMGap/Continuum/PolynomialGeometricDecay.lean:99` supplies the
constructive exponential/polynomial comparison and explicit cutoff.
This tests whether a selected POSITIVE scalar payment with a nonzero fixed
coupling-power term can itself meet an O(1/side) budget, including a
quadratic Taylor prefactor. It supplies no lower bound on an actual energy,
moment or remainder; exact cancellation and sharper estimates remain
possible. It is not a physical-spacing calibration or an obstruction to YM.

Prediction: that scalar budget fails even at arbitrarily high FIXED power;
degree zero must be included. Stop if the statement already exists, the
original schedule is replaced, or the proof needs a new asymptotic premise.
One bounded Sol leaf, independent mathematical review, root sole focused
monitored check, one 20-GiB worker and 12-GiB reserve with fresh dynamic
preflight. No broad build/audit, limit increase, frontier-field change or
generic conclusion-as-input. Observations will be recorded separately.

### Observed result and decision

The selected statement is now kernel-checked on the unchanged schedule:

- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:41`,
  `afGap_linear_floor`: 3*(j+1)*afGap(j)>=1, including index zero.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:84`,
  `afPowerBudgetCutoff`: computed ALL-TAIL cutoff, no existential extraction.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:100`,
  `afPowerBudget_gt`: C<side(j)*afGap(j)^p at EVERY index past that cutoff,
  for every FIXED natural p and arbitrary rational C.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:156`,
  `afPowerBudget_no_uniform_cap`: no eventual cap for a fixed p.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:167`,
  `afPowerBudget_adaptive_le_one`: side(j)*afGap(j)^j<=1 for every j.
  This supplies no control of degree-dependent Taylor constants.

Interpretation: PRUNE fixed-order positive scalar payments alone. Replacing
power two by any other fixed power cannot by itself provide an inverse-block
budget on this schedule. Retain signed cancellations and genuinely adaptive
estimates; neither is refuted or produced by this leaf. In particular
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:151`,
`energy_le_angular_add_quadratic`, retains (1-w)^2*sourceTaylorBudget:
there is no supplied uniform nonzero coefficient or lower bound turning
that actual source-dependent budget into the selected scalar payment.
`JointQuadraticDebt` uses 1-w^(4*side), not literally 1-w; do not equate it
with this quadratic-prefactor screen.

NEXT: the actual JOINT signed cost versus SAME surviving filtered variance,
using the existing window consumer. Any adaptive-order proposal must FIRST
produce the actual interacting remainder with its order/source/volume
constants; no new generic asymptotic wrapper is selected. Main scaling,
continuum survival, physical calibration, OS/QFT, all groups and Clay OPEN.

Verification: Sol's bounded leaf, independent full-source mathematical PASS,
root full-source review, one final focused monitored check on 2026-10-08 UTC.
Preflight found no competing compiler/runner, 87% reported available memory
and zero swap; one worker, hard 20 GiB ceiling, 12 GiB OS reserve. The first
check exposed only missing explicit unfolding of rational one's numerator
and denominator in a private helper; root repaired it without statement or
limit changes. Its failed axiom output is NOT evidence. Final log:
`/private/tmp/ym-af-power-budget-20261008b.log`; cutoff is axiom-free and
all four public theorem gates are exactly {propext, Quot.sound}. Source
SHA256: `857130af1272820cfc6165b713c67cca6a065b63b4af981f2bff597a424564da`.
Root import registered, not rebuilt. No full-root/tree build/audit/guard,
baseline refresh, new sorry/axiom/classical/native shortcut, canonical field
change or broad chart closure/reprint.

## Weighted chronological sign screen (2026-10-08 UTC)

### Follow-on square-completion screen (source review only)

Independent mathematical review and root source inspection, 2026-10-08 UTC.
This is a PAPER reduction, not a new Lean theorem or a produced scaling bound.
Retain T=K*M_V, ell_V=H[V*], a=g_d, A=Ta, z=ell_V[a^2], v=ell_V[A^2],
the supported incoming phi and a spatial insertion Theta. On the original
two-endpoint kernel define

```text
P(x,y) = K(x,y)*V(x)*V(y)*a(x)*A(y)
C      = ell_V[a*phi^2*(T(Theta*A)-Theta*T(A))]
M      = H2[P*phi(x)^2] = ell_V[a*phi^2*T(A)]
JTheta = H2[P*phi(x)^2*(Theta(y)-Theta(x))^2].
```

The original kernel/action/terminal positivity certificates make P positive.
For each positive rational tau, expanding the two literal nonnegative
squares P*(phi(x)*(Theta(y)-Theta(x)) +/- tau*phi(x))^2 gives

```text
  +/- 2*tau*C <= JTheta + tau^2*M.
```

Thus square completion needs no fourth power of phi or source inverse, but
the full chronological residue still contains BOTH the commutator z*C and
ell_V[a*phi^2*Theta*(z*T(A)-v*a)]. This is not a sign or stationary-law pin.
The exact existing SAME endpoint identity is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lean:86`,
`lastStepNoise_endpoint_pin`: M contains innovation PLUS the outgoing source
norm. It is not the surviving variance alone. The actual positive Ward
payment retains the additional spatial insertion T(Vbar*A), by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin`.

No supporting producer bounds the source-weighted action-jump square JTheta
and chronological defect jointly by the required SAME surviving variance.
In particular
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:132`,
`energy_taylor_angular`, has the actual projected source and BOTH outgoing
signed remainders; it does not assert a matching negative JTheta. Do not
substitute its density for P or cancel unlike weights. Decision: retain this
screen as an explicit unpaid moment, not another conditional square-bound
module. The coupled signed window estimate remains OPEN.

Duplicate screen resolved: the suggested converse from represented dyadic
quotient convergence to coordinate range/graph witnesses is ALREADY in
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInputRange.lean:69`,
`inputRange`, and `representedGraphOfQuotientLimit:94`. Do not rebuild it.
No Lean edit, compiler, new hypothesis, canonical field or chart delta from
these source reviews.

Selected proposition: test whether original-form positive weighted transfer,
chronological partitions and OWN centering alone sign the additional weighted
time residue. Its source consumer is the proposed adjacent-stage cancellation
of the positive incoming Ward payment, not a new physical frontier bundle.

Source-level algebra (NOT a new Lean theorem) from
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`,
`transferStep_weighted_symmetric`, generalizes
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lean:86`,
`lastStepNoise_endpoint_pin`. With A=Ta, b=T(a*phi), N=A*T(a*phi^2)-b^2,
z=ell_V(a^2), v=ell_V(A^2), the cleared weighted difference equals

```text
z*(ell_V[Theta_out*N]+ell_V[Theta_out*b^2])
  -v*ell_V[Theta_in*(a*phi)^2]
 = ell_V[a*phi^2*(z*T(Theta_out*A)-v*Theta_in*a)].
```

Setting BOTH Theta weights to Vbar retains
`z*(T(Vbar*A)-Vbar*T(A))+Vbar*(z*T(A)-v*a)`.
Neither the spatial transfer commutator nor the chronological vacuum defect
is removed by partition multiplication. The incoming Ward density genuinely
contains T(Vbar*A): `RatioNoiseWardAbsorption.original_ratioNoise_gradientPayment_weighted_pin`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`.
The complete derivative also retains J(V):
`LastStepSourceDerivative.lastStepSourceDerivative_expansion` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:80`.

NEW CHECKED diagnostic in
`lean/YMGap/Continuum/RationalWeightedTemporalResidueObstruction.lean`:

- `heat_kernel_pin:60`, `transfer_symmetric:75` and `transfer_positive:112`
  certify the actual two-state K=[[3/4,1/4],[1/4,3/4]], V=(2,3), T=K*M_V.
  Weighted symmetry and positivity hold for ALL rational probes, not just
  the counterexample. K has positive entries and unit row mass.
- `chronological_pins:126` computes A=(9/4,11/4), z=5/2 and v=525/32
  from the literal a=1. `own_mean_pin:144` centers f=(1,0) in the actual
  VaA edge law: mass=51/8, mean=6/17. `own_variance_positive:149`
  rules out a degenerate excitation. `noise_pin:163` gives N=(9/8,9/8).
- `centered_residue_pin:154` gives the positive integral 3045/9248.
  `weighted_time_difference_pin:173` retains the extra spatial insertion,
  BOTH computed partitions and complete noise; `weighted_time_difference_positive:174`
  proves that exact difference is positive. No inverse approximation or
  stationary source is substituted.

Decision: PRUNE ONLY automatic nonpositive weighted-telescope residue from
those generic inputs. This d=0 two-state diagnostic is not an SU(2) action,
a positive-filter-depth BF4 counterexample or a refutation of the full two
signed Ward responses plus BOTH Taylor terms. It pays no actual scaling cost.
NEXT remains a source/action-specific JOINT estimate against the SAME surviving
variance, consumed by `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`. The parallel projected-q^2 Ward screen
also supplied no favorable sign or useful joint inequality; no raw-q^2
standalone cap is promoted to a necessary hypothesis.

Root complete-source and independent complete-source mathematical reviews PASS.
One focused monitored check passes; all 17 printed gates are permitted (13
axiom-free, four exactly {propext, Quot.sound}). Final log:

```text
/private/tmp/ym-weighted-temporal-residue-20261008a.log
SHA256 4de38b69e80606ee038d574dd6f547c611a4a3d24044a9b95869f7bd00c64396
```

Fresh preflight: no competing compiler, 87% system-wide free and zero swap.
One worker, hard 20-GiB ceiling and 12-GiB reserve. Root import registered only;
no root/full-tree build, audit, guard, baseline refresh, hole, axiom or canonical
field change. Broad chart claims unchanged; no reprint.

## Live source reconciliation and checked SAME-OWN contraction (2026-10-08 UTC)

Historical NEXT entries in this audit do not override the current source.
Current-source independent reviews find the scalar addition-square, radial
ceiling and their original-prefix Haar/frozen joins already constructed:
`lean/YMGap/Continuum/ThetaCompletedAdditionSquare.lean:179`,
`cleared_addition_square`;
`lean/YMGap/Continuum/ThetaProductRadialCeiling.lean:112`,
`productRadialCost_le_cap_add_tail`;
`lean/YMGap/Continuum/JacobiHeatRadialHaarCertificate.lean:182`,
`radialCertificate`; and
`lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:88`,
`prefix_frozen_curvature_adaptive_certificate`.
Those are existing producers, not new checks in this checkpoint. Do not build
another tail/addition/strict-floor wrapper. The actual missing quantitative
input remains joint original action/source response control, including the
retained density/spatial derivatives, reconstruction/drift and BOTH Taylor
remainders against the SAME surviving filtered variance. The concrete consumer
is `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`.

Selected mathematical increment: contract the existing connected-Gram raw
mixed moment, rather than require a standalone raw-to-OWN ceiling. Available
inputs: the literal symmetric sum test, SAME product heat pairing/symmetry,
original projected-source energy and OWN centered-square pins. Pointwise,

```text
(q+q')^2*(psi+psi')^2
  = (q-q')^2*(psi+psi')^2 + 4*q*q'*(psi+psi')^2.
```

The second integral equals 8*S+8*B=16*S-8*E. No source positivity,
stationary eigenpin, normalized-law substitution, source/variance inverse or
new analytic premise is needed. Test arbitrary supported sources, zero
denominators/depth zero, actual observable fringe guards and BOTH mean
corrections. Verification budget: two serialized narrow 20-GiB checks, root
sole compiler, independent complete-source review. Stop on a source/energy
substitution or a claimed positive credit from Gram positivity alone.

Observed VERIFIED PROGRESS:

- `lean/YMGap/Continuum/SU2QuaternionProductHeatSumNorm.lean:229`,
  `sourceSumIncrementCost`, defines literal Dplus=H[K*(jump q)^2*(sum psi)^2].
  `sourceSumIncrementCost_nonnegative:235` produces Dplus>=0 from the actual
  product-heat certificate; `sumTest_norm_energy_pin:256` proves the exact
  16*S-8*E+Dplus norm. The heat list and every supported factor remain.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:292`,
  `centered_sourceSumIncrement_nonnegative`, instantiates that residue on the
  actual projected endpoint and OWN center. `centered_norm_energy_pin:308`
  supplies S=oddMass*OWN oddVariance and the ORIGINAL energy. Explicit
  observable fringe independence is retained; no raw-q^2 mean is substituted.
  `centered_denominator_energy_pin:350` keeps the actual -M^2, giving
  V=16*S-8*E+Dplus-M^2. `original_centered_energy_response_budget:370`
  consumes it in the existing 4*V*E+V*J^2+X^2<=2*V*C inequality, with
  unchanged J, M and X=Cov(r,s). Degenerate V remains covered; no division.

Decision: CONTINUE joint response control. Dplus>=0 is not an upper estimate
for V, so this identity alone pays no useful fraction. It removes the need to
express the residue as an independently bounded raw mixed moment; it does
not make that moment comparison automatic. A joint credit may retain
X^2-(Dplus-M^2)*Var(r); no lower bound on it is proved here. No initial-energy,
filtered-survival, scaling or completed physical/Clay node is closed. The
separate cofinal AF necessity shows why a useful initial fraction on the
unfiltered square schedule needs large original cancellation; see the
interacting-response-shape audit. Keep unfiltered and filtered norms distinct.

Root inspected the complete final sources; independent complete-source
mathematical review PASS. Both final focused checks pass, all seven new
printed declarations stay within {propext, Quot.sound}. Unlike the AF probe,
the sourceSumIncrementCost definition has permitted dependencies; it is not
reported axiom-free. Logs:

```text
/private/tmp/ym-source-sum-energy-pin-20261008a.log
SHA256 be05611ef4fdd5ca36288750118b7497e06a5ddcf43db2d7639787acc60481a7

/private/tmp/ym-own-source-response-denominator-20261008a.log
SHA256 53481cb7f24b793e70e92ea22bc20cd2c852bb4ffb69af904478b39bf6abed94
```

Fresh preflights found no competing compiler/runner, 88% system-wide free
and zero swap. One worker, hard 20-GiB ceiling and 12-GiB reserve; no limit
increase. No new imports in the two leaves, no full-root/tree build/audit,
baseline refresh, sorry/axiom, canonical field change or chart reprint.

## Selected reciprocal-free positive gradient payment (2026-10-08 UTC)

### Selected exact incoming-density trace (2026-10-08 UTC)

Next bounded identity: `H[Vbar^2*A*T(a*(Jphi)^2)]`
`=ell_V[a*(Jphi)^2*T(Vbar*A)]`, with a=g_d and A=Ta. Produce fringe
independence of the transferred gradient square, apply actual fringe Fubini
and ORIGINAL weighted transfer symmetry. No sign or nome/cutoff positivity
is needed. Consumer: the checked unit-gradient Ward payment can be expressed
in original incoming coordinates without identifying it with another density.
Prediction: BOTH the active Vbar factor and the additional temporal step
remain. Actual marginalAngular uses a*Ta, not a*T(Vbar*Ta). Thus a direct
coefficient-one marginal-energy/variance join is unavailable. Stop if the
pin drops Vbar, identifies T(Vbar*A) with A/TA, or silently uses raw-family
gradient control for the filtered reconstructed ratio. One existing changed
leaf, independent review, root-only monitored 20-GiB check; no new interface.

Observed: VERIFIED exact incoming-density identity. In
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin` proves the displayed pin
for arbitrary rational nome/cutoff and supported phi. Phi need NOT be fringe
independent: independence of Ephi is produced by the actual transfer image.
Both the original spatial weight V and the literal T(Vbar*A) survive.
Final focused check `/private/tmp/ym-ratio-noise-incoming-density-20261008a.log`
passes all six printed gates exactly {propext, Quot.sound}; source SHA256
`272d9b089299597e99bf2f9b87b6c4f46b574be346c3d9b0ddb07020f0428512`.
Independent full-block review PASS. Preflight: 87% system-wide free, zero swap,
no competing compiler; one 20-GiB worker/12-GiB reserve. No full-tree audit,
new hypothesis bundle, hole, axiom or canonical field/diagram closure.

Decision: PRUNE the direct coefficient-one identification with marginalAngular
or normalizedEnergy. This is not a refutation of a possible joint signed
bound. The actual incoming marginal angular density is V*a*Ta:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAngularMarginal.lean:51`,
`marginalAngular`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:130`,
`marginal_middleRatio`, pins its original chronological law. Even an ordinary
spatial cap first gives T(Vbar*A)<=C*T(A)=C*T^2a, so a further terminal
comparison is needed; neither factor is coefficient one or a useful scaling
estimate. Do NOT implement that coarse ceiling as another claimed producer.

Existing Taylor rebasing does not supply the missing cancellation (SOURCE
REVIEW, not an impossibility theorem). `AngularMarginal.angular_weight_identity:104`
converts q_d^2*Gamma(f) to q_d*P(q_d)*Gamma(f) for the SAME source and f.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalTaylor.lean:64`,
`signedRemainder`, retains that defect; `energy_taylor_marginal:71` performs
that rebasing, not a removal of Vbar inside a subsequent transfer.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean:235`,
`exactScoreAngularBudget_terminal_signed_payment_le`, uses incoming phi at n,r;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:218`,
`exactScoreSignedBulk`, retains outgoing phi at n,r+1 and its own numerator,
reciprocal degree and BOTH Taylor terms. Those observables are not equal.
CONTINUE only with action/source-specific JOINT control across these literal
transitions, or an independent actual signed response credit. No supplied
conclusion, raw Wilson Casimir substitution or changing-family survival claim.

Independent frozen-source operator-view screen (2026-10-08 UTC, source review
only): `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`,
`energy_identity`, already pins twice the original energy to the division-free
edge jump form. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lean:201`,
`lastStepPredictionResidual_energy_pin`, retains the original diagonal V*a*Ta.
Neither statement compares that measure with the next V*Ta*T^2a or bounds
the unpaid coupled Ward/Taylor expression in the next surviving norm.
Do not re-export these identities as a new scaling producer. The alternate
initial-energy consumer already exists at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
`original_block_cost_le_initial_energy`; its literal `hlocal` input remains
to be produced with a useful changing-family fraction. No new Doob wrapper,
conditional frontier field or proof claim is added by this screen.

Independent SU(2)-harmonic response screen (2026-10-08 UTC, source review
only): `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:248`,
`productMap_fundamental_word`, pins the bare ordered fundamental word, not
the interacting product q*F. The literal source in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:60`,
`squareHeatMultiplicationDefect`, retains q=V*terminalMessage;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`,
`spatialWeight`, and `BF4ExactSlabFixedSpatialTransferStep.lean:51`,
`transferStep`, reinsert the full spatial action before heat smoothing.
No bounded-spin hypothesis for q or reconstructed filtered ratios is produced.
The exact unpaid response is retained by
`BF4DyadicWilsonSquareSignedHeatDefect.lean:129`,
`paddedSquare_energy_signedHeatDefect_identity`:
E=(1-w^(12*side))*S-signedGain, with S=oddMass*OWN oddVariance.
The existing all-index AF loss budget
`BF4WilsonAllNomeAFPaddedTrajectory.lean:461`,
`af_squareLinearHeatBudget_ge_one`, and
`BF4DyadicWilsonSquareBareTransmissionNecessary.lean:74`,
`bare_transmission_floor_necessary`, imply on paper that this bare
transmission is at most 1/2. Thus a useful E<=c*S requires a positive
interaction gain at least (1/2-c)*S, not just a small absolute remainder.
This consequence is a source-level mathematical screen, NOT a newly checked
Lean theorem, energy lower bound or obstruction to Yang--Mills itself.
`BF4DyadicWilsonSquareWardMoments.lean:385`, `paddedSquare_ward`, computes
the literal Ward moments but supplies neither their useful joint sign nor
their complete remainder estimate. Do not import the bare eigenpin into the
different incoming weight V*a*T(Vbar*Ta). CONTINUE action-specific JOINT
response/Taylor control; no new harmonic-response wrapper is justified.

Independent localized-pair screen (2026-10-08 UTC, source review only):
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:208`,
`original_centered_energy_budget`, retains actual
q=projectedEndpointSource w K width (terminalMessage w K width depth), psi=F-OWNmean,
r=(q-q')*(F-F') and s=(q+q')*(psi+psi'). Their product can be expanded on
paper as (q^2-q'^2)*(psi^2-psi'^2); bare character transmission then concerns
raw projected-source q^2 moments, NOT automatically the OWN qPq moments in
`BF4DyadicWilsonSquareWardMoments.lean:385`, `paddedSquare_ward`.
`BF4ExactSlabFixedSpatialSourceVarianceGram.lean:138`,
`centeredNormExpression`, and `centered_sum_norm:145` retain the complete
sourceIncrementCost, centeredMixedMoment and interacting variance. The
nonnegativity theorem `centered_denominator_nonnegative:175` is not their
useful upper comparison. No source-level raw-to-OWN moment or localized
mean-crossing payment was found in this inspected route. The existing
positive spectator-band response
`BF4DyadicWilsonSquareSpectatorResponse.lean:237`,
`paddedSquare_energy_band_cleared`, is not a new order-one gain producer.
These are source/math reviews, not newly checked Lean response identities,
integrated energy lower bounds or an obstruction to the BF4/Yang--Mills
estimate. Do not add a localized-certificate interface assuming the missing
statistical payment. The actual JOINT relative response estimate remains
the primary frontier.

Bounded estimate: on ACTUAL a=g_d, A=Ta, Ephi=T(a*(Jphi)^2), Vbar and
the existing finite G_k(A), test H[Vbar^2*G_k^2*A^3*Ephi]
<=H[Vbar^2*A*Ephi], coefficient ONE for every finite k. Produce the A
window, A/Ephi positivity and multiply the existing certificate
1-(A*G_k)^2 by Vbar^2*A*Ephi. No precision onset, floor penalty, new source
inverse, historical-noise widening or action replacement. Prediction: the
only positive gradient payment in the actual Ward consumer loses its
outgoing-degree dependence; both signed G_k-dependent responses remain.
This is not smallness relative to surviving variance. Root bounded extension
of the existing leaf, independent review, one narrow monitored 20-GiB check.
Stop if Ephi positivity is not produced or either signed response is dropped.

### Observed result / decision

VERIFIED PROGRESS: the existing Ward leaf now proves
`original_ratioNoise_gradientPayment_unit_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:253`.
Actual terminal/transfer certificates produce positivity of A and Ephi and
the actual output window, including d=0. The positive difference is certified
as `Vbar^2*A*Ephi*(1-(A*G_k)^2)`, for EVERY k including zero.
`original_ratioNoise_ward_unitGradient_le:323` consumes it at k+1 and retains
BOTH signed responses verbatim. No precision onset or numerical floor loss
remains in this positive payment. Discarding the finite multiplier is an
upper-envelope simplification, NOT a sharper numerical bound.

Final focused check: `/private/tmp/ym-ratio-noise-unit-gradient-20261008b.log`,
all five printed gates exactly {propext, Quot.sound}. Final source SHA256:
`f5ccbf8493173599d98038c793ef6f0af953ca7c2afcac1af247d489aea9c697`.
Independent complete-block review PASS. Fresh preflights: 87--88% system-wide
free, zero swap, no competing compiler; one 20-GiB worker/12-GiB reserve.
No full-tree check, new hole/axiom, field weakening or chart-claim change.

KEEP the new literal consumer. The bare positive payment is still an ORIGINAL
interacting incoming-gradient moment, not the SAME surviving variance. The
two signed density/spatial responses retain G_(k+1). Their useful joint
source-specific comparison, reconstruction/drift and BOTH signed Taylor
remainders remain the next producer for `original_window_budget_macro_ratio`.
Independent source review found no supplied initial O(1/u) energy fraction;
posterior mixture score variance is not removed by component log concavity,
and the raw Wilson Casimir does not bound the reconstructed filtered ratio.
These last route screens are source review, not new Lean estimates.

## Observed noise derivative and ONE-cross Ward absorption (2026-10-08 UTC)

Classification: VERIFIED PROGRESS for the following finite original-source
identity/estimates; SOURCE-LEVEL REVIEW ONLY for the joint-IBP screening below.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseDerivative.lean:171`,
`ratioNoise_derivative_carrier`, proves the pre-registered cleared identity
with complete g=V*a, actual K, A=Ta, b=T(a*phi), U=T(a*phi^2), N=AU-b^2
and X=lift(A)*phi-lift(b). It preserves EVERY surviving insertion.
`weightedNoise_derivative_carrier:243` retains arbitrary output V and J(V^2N).
It assumes no positivity, exact ratio/inverse or stationarity.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.lean:195`,
`original_ratioNoise_phiGradient_absorption_le`, produces the ACTUAL terminal
law and its positive window. Its conditional square is
I[K*g*(lift(JA)*X+lift(A^2)*Jphi)^2]
=A*(N*(JA)^2+2*A*(JA)*Mphi+A^3*Ephi).
Positive-multiplier reflection gives
-H[R*(N*(JA)^2+2*A*(JA)*Mphi)]<=H[R*A^3*Ephi]
for arbitrary certified R. Coefficient ONE; no N/A inverse or lower-floor
factor in the bound. Reflection is integrated order, not division of a
certificate. `ratioNoiseGradientMoment:68` and `ratioNoiseGradientEnergy:74`
retain literal original incoming moments. Depth d=0 is permitted because
the produced output window is for g_(d+1).

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:115`,
`original_ratioNoise_ward_absorption_le`, uses the ACTUAL successor reciprocal
G_(k+1)(A), Vbar=spatialFringeMass, F=Vbar^2*N and R=Vbar^2*G^2. Noise,
output certificates and the upper window are PRODUCED. The one-plane result is
H[F*G^2*(A*J^2(A)-(JA)^2)]
<=H[R*A^3*Ephi]-H[R*(JA)*I[K*(Jg)*X^2]]
  -2*H[A*G^2*(JA)*Vbar*(JVbar)*N].
`ratioNoiseDensityMoment:57` retains FULL J(V*a), and
`noiseDerivativeIncoming_moment_pin:65` proves the exact density+2*A*Mphi
split. Input V and output Vbar remain distinct. Incoming phi is arbitrary
supported data; no incoming/outgoing reciprocal-degree identification.

Root and independent complete-source mathematical reviews PASS. Final
focused logs PASS, all 13 printed gates exactly {propext, Quot.sound}:
`/private/tmp/ym-ratio-noise-derivative-20261008b.log` (seven),
`/private/tmp/ym-ratio-noise-absorption-20261008c.log` (three),
`/private/tmp/ym-ratio-noise-ward-20261008a.log` (three).
Earlier checks exposed namespace, negation-support, proof-composition,
transport-orientation and reflexivity elaboration typos; their repairs change
no theorem statement or resource limit. Failed-check output is NOT evidence.
Fresh preflight before EVERY launch: 87--88% free, zero swap, no competing
Lean/Lake/pytest/runner. One 20-GiB worker/12-GiB reserve, root sole compiler.
Root imports registered only; no root/tree build, full audit/guard or baseline
refresh. No source sorry/new axiom/classical/native shortcut or field weakening.
Checked-source SHA256 (Derivative / GradientAbsorption / WardAbsorption):
`515795cba822f9e9e1d3df9ec571215089befa358bd0dc44f8bbeac2724a82d2`,
`dd788690bf2a8d51a32e8b2c4fddeadbc15f47a28dba49e4543407b667ddf92e`,
`bd9ebc8a0dcf9daa3e9bffee2894e4f37572f6c86d49798be76afdb3334b80d3`.

### Decision / next actual estimate

KEEP the coefficient-one payment and literal signed responses. REPOINT to
action/source-specific coercivity or cancellation controlling them jointly
with the incoming-gradient payment, reconstruction, drift and BOTH signed
Taylor remainders on the filtered OWN-centered padded Wilson family.
The actual aggregate input remains
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`: an eventual normalized original-window
cost bound against the SAME surviving variance. Its chronological partitions
remain distinct; no universal arbitrary-source noise cap is requested.

Independent source-level screening combines the two retained signed terms
on the actual edge as -H2[K*G_y^2*D_y*X^2*(J_x+J_y)(g_x*Vbar_y^2)].
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularForm.lean:64`,
`productHeat_pairedAngular_carrier`, removes the simultaneous K derivative,
not the action derivative. Joint Haar IBP then reintroduces the paid phi
cross and returns to the existing Ward identity. This is NOT a newly checked
bound or counterexample; PRUNE implementing that circular rearrangement.
Fringe independence permits conditional integration, not active-link action
derivative cancellation. OWN centering supplies a global moment constraint,
not a sign for this innovation-weighted density term. The separate gauge
review likewise found no symmetry-only linkwise orthogonality/cancellation.

No useful initial energy fraction, complete surviving-form scaling estimate,
continuum survival, completed OS, physical mass, SAME limiting QFT, every-group
or Clay claim closes. Canonical displayed claims are unchanged; no chart reprint.
The user's measurement guidance is already incorporated with primary-source
corrections in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; numerical
channel masses provide no premise or replacement for these analytic inputs.

## Selected absorption of the incoming observable-gradient cross (2026-10-08 UTC)

Bounded estimate to test after the derivative pin: with the same actual
g=V*a, A=T(a), N, X, define M=I[K*g*X*J_in(phi)] and
E=I[K*g*(J_in(phi))^2]. The square
I[K*g*(lift(J(A))*X+lift(A^2)*J_in(phi))^2]
expands to A*(N*J(A)^2+2*A*J(A)*M+A^3*E).
For ACTUAL terminal a and its PRODUCED positive A window, reflect that
multiplier inside Haar order to obtain, for certified R,
-H[R*(N*J(A)^2+2*A*J(A)*M)]<=H[R*A^3*E].
Prediction: coefficient ONE, no inverse of N or A and no lower-floor loss
in the estimate. Existing partial-square positivity and quantitative
positive-multiplier reflection are the intended inputs.

Consumer: the favorable negative square exposed by the weighted derivative
pin absorbs precisely its incoming observable-gradient cross. The spatial
and COMPLETE incoming-density derivative terms remain signed and OPEN;
no initial energy fraction, surviving-form bound or scaling result follows.
One bounded implementation leaf with an actual terminal consumer that
PRODUCES its window/positivity, independent source review and root serialized
narrow 20-GiB verification. Stop or revise if the square loses a factor of A,
the reflected weight is not produced, or a noise/source inverse is introduced.

## Selected incoming noise-derivative experiment (2026-10-08 UTC)

Proposition: let g=V*a on LOWER coordinates, A=T(a), b=T(a*phi),
U=T(a*phi^2), N=A*U-b^2 and X=lift(A)*phi-lift(b). At arbitrary-insertion
Haar-carrier strength, test the division-free identity
A*J(N)-N*J(A)=I[K*((J_in g)*X^2+2*g*lift(A)*X*J_in(phi))].
The input/output derivatives are distinct. The actual kinetic K and complete
spatial action V remain. Available inputs: original product-heat angular
commutation, exact Leibniz rules and ordered-head lifted-factor pullout.
No positivity, marginal inverse, exact source ratio, stationarity or derivative
sign is assumed. This is a new nonlinear noise moment, not the existing
linear score-source pin.

SAME-object consumer: `QuaternionHaarPairedHessianTrace.
finite_reciprocal_paired_hessian_ibp_le` retains J(F), F=Vbar^2*N.
The predicted identity rewrites A*J(F) as
F*J(A)+2*A*Vbar*J(Vbar)*N+Vbar^2*Q, where Q is the actual incoming moment
above. It exposes a favorable negative marginal-score square, the original
spatial cross term and the COMPLETE signed incoming source cross term.
These cross terms must still be controlled relative to the surviving form;
the identity itself does not supply the missing estimate.

Prediction: exact carrier identity from three transported moment jets and
a single quadratic residual expansion. Revise if an output derivative is
confused with an input derivative, lifted factors cannot be pulled through
the actual head integral, or required strength is reduced to unit testing.
One bounded Sol implementation leaf, independent mathematical/source review,
root sole narrow compiler with fresh dynamic preflight, one 20-GiB worker
and 12-GiB reserve. No broad build/audit/guard or field changes. Parallel
read-only review tests genuine gauge-vertex Ward cancellation; individual
link derivatives of V are not assumed zero.

## Observed selected coefficient / next estimate (2026-10-08 UTC)

Classification: VERIFIED PROGRESS for the rational scaling screen;
SOURCE-LEVEL MATHEMATICAL REVIEW ONLY for the alternative-route analysis.

`lean/YMGap/Continuum/SU2QuaternionPairedPrefixCostScaling.lean`:
`normalizedPairedPrefixCost:29` defines the literal H=3*(1-w)*C(w).
`normalizedPairedPrefixCost_excess_cleared_pin:70` gives
(1+w)*(H-9)=3*(1-w)*(2*w+3).
`normalizedPairedPrefixCost_pin:100` gives the exact divided formula,
`normalizedPairedPrefixCost_excess_bounds:138` gives 0<=H-9<=9*(1-w),
and `normalizedPairedPrefixCost_lower:170` gives 9<=H.
The explicit rational error bound permits any prescribed tolerance epsilon
once 9*(1-w)<=epsilon; no CReal limit oracle or trajectory is assumed.

Final focused log `/private/tmp/ym-paired-prefix-cost-scaling-20261008b.log`
PASS: data definition axiom-free, four gates exactly {propext, Quot.sound}.
Root read the complete source and independently checked the formula/order;
parallel complete-source review found no substantive defect. The first check
failed on an extra explicit argument to eqv_symm; the one-line repair changed
no statement or limits. Failed-check sorryAx output is not proof evidence.
Checked-source SHA256:
`c690d452522a7cdd04c6239fabf87f4f66f27a61daf34f1be60659f492a08733`.
Fresh process/memory/swap preflight before both launches: 87--88% free,
zero swap, no competing Lean/Lake/pytest/runner. One 20-GiB worker,
12-GiB reserve. Root import registered, not root-built; no full-tree build,
audit/guard or baseline refresh. Canonical chart claims remain OPEN.

Decision: PRUNE smallness from the nome prefactor alone on THIS chosen
coefficient. Its bound is not a lower bound on a noise moment, actual score,
energy or signed bulk. The existing sharper adaptive cost remains available:
`lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:88`,
`prefix_frozen_curvature_adaptive_certificate`, retains radialCap(w,K+1)+2.
Do not advertise nine as an inherent obstruction to SU(2), the route, or YM.
Keep the signed terms and test the actual aggregate consumer instead.

### Parallel route reviews and exact normalization guard

No concrete useful initial padded-Wilson energy producer was found in the
inspected LocalEnergyTransport, SourceRayleighPersistence, SourceTaylor,
FiniteReferenceMargin, WidthOneSource, FringeFaceTransfer and
NoiseSurvivalObstruction modules. The conditional producers are not weakened:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
`original_block_cost_le_initial_energy`, consumes its INITIAL fraction;
`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:317`,
`Certificate.reference_ratio`, consumes accepted finite reference data.
The existing width-one inactive Wilson face has a null transmitted centered
source (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialNoiseSurvivalObstruction.lean:133`,
`origin_transmitted_pair_zero`). It cannot supply a near-unit Rayleigh floor
merely from large nome. It is not the strictly padded active source required
by the actual window; no selected-family counterexample was established.

The already checked exact cancellation is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy.lean:170`,
`exactScoreSignedBulk_energy_split`: BOTH signed Taylor terms reassemble to
the NEXT-edge energy plus the signed finite reciprocal debt. The matched
noise is instead a PREVIOUS-step variance:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:138`,
`blockNoise_variance_loss`, pins its distinct chronological square.
Incoming k and outgoing l are independent in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean:235`,
`exactScoreAngularBudget_terminal_signed_payment_le`.
At incoming k=0 the reciprocal/ratio definitions give zero reconstructed
source/noise, without making outgoing l's actual score/Taylor terms zero
(`lean/YMGap/Continuum/QuaternionHaarPositiveWindowInverse.lean:162`,
`reciprocal`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:213`,
`blockConditionalRatio`). Thus reconstruction and Gram slack cannot be
silently removed from a putative exact cancellation. This is a source-level
scope test, not a new checked counterexample.

NEXT: the aggregate actual normalized cost remains the required estimate,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`. A direct NEXT-edge route must retain
the exact split in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`,
`clearedRayleighCost_split`:
D=Z0*E(A,phi)+boundaryDrift+signedMultiplicationCost.
With `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`,
`energy_identity`, the resulting PAPER reduction is
2*Cost=H_edge[edgeDensity(A)*jump(phi)^2]/Z1
        +2*(boundaryDrift+signedMultiplicationCost)/(Z0*Z1).
Every t has its OWN distinct Z0,Z1. The reconstructed phi, its support,
finite reconstruction onset and boundary drift stay explicit; no finite
stationarity or exact b/A is assumed. Controlling the aggregate of this
complete expression, or the original signed Gram expression, on the
literal OWN-centered padded scaling family remains OPEN. No new interface,
unsupplied conclusion-as-input or universal noise cap was introduced.

## Selected weak-nome cost screen (2026-10-08 UTC)

Proposition to check: for the EXISTING selected cost C=prefixCurvatureCost(w),
the THREE-paired coefficient H=3*(1-w)*C satisfies
H-9=3*(1-w)*(2*w+3)/(1+w), hence 9<=H<=9+9*(1-w) at each strict nome.
Consumer: the three constant-basis terms in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean:127`,
`terminalSignedGramPayment`, followed by the actual (1-w) Taylor prefactor in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:218`,
`exactScoreSignedBulk`. Inputs: the literal geometric definitions of the
existing transverse and cutoff-independent radial envelopes. This tests
whether weak nome alone makes that chosen leading coefficient small; it
does NOT test the complete signed payment, actual noise scaling, a sharper
curvature certificate, or the Yang--Mills mass-gap claim.

Predicted outcome: a nonzero limiting coefficient, with an explicit rational
error bound. Abandon or revise the prediction if the actual definitions differ.
One bounded Sol leaf, root full mathematical review, one narrow monitored
20-GiB-worker check with fresh capacity preflight and a 12-GiB reserve;
no broad build/audit/guard. The separate parallel reviews test an ACTUAL
padded-Wilson initial-energy producer and exact Ward/Taylor cancellation,
before adding any more conditional interfaces. Results below will distinguish
new checked evidence from source-level arguments.

## Observed paired Ward trace / filtered-family scope (2026-10-08 UTC)

Classification: VERIFIED PROGRESS for the trace; SOURCE-LEVEL MATHEMATICAL
REVIEW ONLY for the newly composed null-source screen below.

`lean/YMGap/Continuum/QuaternionHaarPairedHessianTrace.lean`:
`paired_gradient_mixed_pin:80`, `paired_gradient_square_pin:113` are raw
coefficient identities for two wedges sharing the SAME coordinate vector.
`paired_second_trace_carrier:172` uses arbitrary-insertion Haar IBP and
stays at carrier strength; `paired_hessian_trace_carrier:220` therefore
retains the full signed trace. `finite_reciprocal_paired_hessian_ibp_le:260`
consumes the ACTUAL successor reciprocal and yields the selected literal
negative SIX-plane derivative sum. Leading THREE-basis curvature payment
is not replaced by SIX. No radius identity, inverse or Hessian-sign premise.

Final focused log `/private/tmp/ym-paired-hessian-trace-20261008c.log` PASS;
five gates exactly {propext, Quot.sound}. Root read the full final source;
independent mathematical review found no substantive defect. Initial implicit
trace inference timeout was repaired by explicitly typed intermediate moments
and explicit carrier parameters, not a limit increase. Failed-check kernel/
axiom output is not evidence. Checked-source SHA256:
`e7ccf9b26b6daf0b13f427ef7af66bf29076258975d3babc72112e81ebabf1b1`.
Fresh capacity preflight before every launch, one 20-GiB worker/12-GiB
reserve, 87--88% free and zero swap. Root import registered only;
no broad build/audit/guard or baseline refresh. Broad chart unchanged.

### Null-source review and the actual required quantifiers

This is a PAPER DERIVATION from the cited APIs, not a newly checked theorem.
For width one, n=1,r=0 and incoming/outgoing degrees ONE, source review
predicts Vbar equivalent to 1 and A equivalent to 1 under supported Haar
tests, while the FULL spatial V remains unchanged. The finite incoming
phi_1 is alpha_in*originSource on that carrier, alpha_in>0. Thus its matched
noise is alpha_in^2 times the old noise; angular A derivatives vanish and
the Ward correction is zero. The remaining three C*noise upper payments
are positive although the actual score and complete signed bulk are zero.
This prevents inferring an arbitrary-source surviving cap from the new upper
bound; it does NOT refute the bound itself.

Source pins checked by read-only review:

- `lean/YMGap/Continuum/BF4ExactSlabWidthOneGeometry.lean:75`,
  `activeSpatialFaces_one`;
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:140`,
  `spatialFringeMass_haar_active`;
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:87`,
  `original_transfer_haar_active`;
  `lean/YMGap/Continuum/SU2QuaternionProductHeatConstant.lean:59`,
  `productMap_one`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceTransfer.lean:133`,
  `spatial_fringe_face_moment`, and
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:64`,
  `marginalMoment_pin`, supply the OWN-center identification in the review.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialNoiseSurvivalObstruction.lean:253`,
  `origin_weighted_noise_positive`, and
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:198`,
  `origin_exactScoreAngularBudget_zero`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:208`,
  `origin_exactScoreSignedBulk_zero`, are the existing positive-noise and
  zero-ACTUAL-score/bulk facts. These are not themselves the new phi_1 pin.

The scope check changes the next target, not a canonical field:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:181`,
`origin_transmitted_null`, annihilates this
particular incoming source after one transfer. Further filtering r>=1 then
annihilates its incoming numerator, finite phi_k and matched noise on the
carrier; that propagation is part of the paper review, not a new proof.
Do not confuse the historical accumulated blockNoise with this matched
reconstructed noise. No counterexample on the filtered range is established.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceRayleighPersistence.lean:266`,
`sourceRayleigh_floor_persists`, CONSUMES an initial floor (it produces
neither a positive floor nor a positive initial norm).
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
`original_block_cost_le_initial_energy`, similarly consumes its useful
initial-energy fraction. Both allow zero filter length in their statements.
The actual backward consumer is
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`: its hbudget concerns the eventual
literal original window, not a universal arbitrary-source noise cap.

Decision: target the literal filtered, OWN-centered padded source and complete
signed cost along its justified family, preserving initial floor/energy
obligations as OPEN. Do not reinstate the refuted universal cap, extrapolate
the r=0 witness to later filters, or treat the source-specific producer as
supplied. The actual spatial/noise Ward derivative, incoming errors and BOTH
Taylor remainders still need their useful combined estimate. All physical/
continuum/OS/full QFT/every-group/Clay claims remain OPEN; no chart reprint.

## Selected trace join and decisive null-source screen (2026-10-08 UTC)

Trace proposition: the mixed paired-gradient product is the SIX-plane
product at raw coefficient strength, by bilinear polarization of two
decomposable wedges sharing the SAME coordinate vector. Haar IBP under
arbitrary insertions then identifies the THREE paired second trace with
the SIX-plane second trace at carrier strength. Together these identify
the entire signed Hessian trace. Consumer: the current matched THREE-row
Gram payment and the checked one-plane finite reciprocal Ward estimate;
leading curvature cost stays THREE, not SIX. No radius premise or
self-coordinate padding collapse. A bounded reviewer leaf is inspected in
full by root and checked with fresh capacity preflight, one 20-GiB worker,
12-GiB reserve; no broad build or options increase.

Decisive screen selected in parallel: re-use the ACTUAL width-one null
source, but first pin the finite reconstructed phi rather than substituting
the older noise witness. A valid signed upper estimate need not be a useful
surviving-norm cap. Check the original incoming k=1 and outgoing l=1,
and retain full spatial V (not Vbar) in original marginal/OWN-center pins.
No sign/relative bound is claimed before those identities are verified.

Bounded consumer extension: apply the signed trace equality at literal
F*G^2, distribute the SIX-plane signed trace coefficientwise and sum the
already proved one-plane Ward inequalities. The new paired upper bound
retains the NEGATIVE SIX-value sum of H[A*G^2*Dij(A)*Dij(F)]. No new
analytic premise, radius identity or lower-floor inverse is used.

## Observed SAME global exact-score consumer (2026-10-08 UTC)

Classification: VERIFIED PROGRESS, no broad chart closure. In
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean`,
`constantPairedBasis:62`, `terminalSignedGramTerm:110`,
`terminalSignedGramPayment:127` and
`original_lastStep_terminal_signed_score_payment_le:162` compose the
SIX original reconstructed plane scores with THREE literal paired Gram
payments and SIX unchanged incoming error payments. No factor two or
leading coarse cap enters. Basis directions are constant and frozen.

`exactScoreAngularBudget_terminal_signed_payment_le:235` produces the
literal W=Vbar^2*Gout_l^2 certificate, pins the actual outgoing source and
terminal at r+1, and feeds every active row of the existing global budget.
Incoming k/outgoing l are independent. Sigma>=0 gives its nonnegative
1+sigma multiplier. No active-count ceiling replaces the signed payment.

Final focused log `/private/tmp/ym-terminal-signed-payment-20261008c.log`
PASS, five printed gates: constant basis axiom-free, four other gates exactly
{propext, Quot.sound}. Root read the full final source; independent review
found no substantive defect in both row and global consumers. One let-bound
rewrite error in the appended global consumer was repaired by explicit
`dsimp only`, not a limit increase; failed-check output is not evidence.
Source SHA256:
`4ba4e141330bb13952845855f0e9ac62e00d83aca8fa9bfe824b755f051664db`.
Fresh preflight before each check, one 20-GiB worker/12-GiB reserve,
87% free and zero swap. Root import registered only; no full build/audit/
guard or baseline refresh.

Decision: CONTINUE through the paired-to-six-plane Ward trace, then seek
a useful estimate for the combined actual spatial/noise derivative, incoming
errors and BOTH signed Taylor remainders relative to SAME surviving form.
No noise-to-surviving-square hypothesis is adopted. This global consumer
does not bound its signed payment by that surviving form. Scaling,
independent survival, completed OS, physical time/volume, SAME full QFT,
every-group and Clay remain OPEN. Broad chart unchanged, no reprint.

## Selected composition: actual SIX scores / THREE signed payments (2026-10-08 UTC)

Proposition: for the SAME original incoming source and arbitrary certified
output W, retain SIX reconstructed angular score squares, and pay their
leading sum by THREE constant paired-direction matched Gram terms, plus
SIX copies of the existing incoming error. Consumer: the existing original
angular/exact-score budget with literal outgoing reciprocal weight.
Inputs are now checked: retained leading reconstruction, matched terminal
Gram and coefficient-exact paired-square/six-square identity. No new
analytic input. Test cost multiplicity THREE, error multiplicity SIX,
constant basis (not polynomial vector-field derivatives), actual c and
finite phi_k reconstruction, arbitrary W and unchanged original action.
Abandon if a factor two, noise cap or different action/weight is smuggled
in. One bounded Sol leaf, full root review, narrow monitored check with
fresh capacity preflight, one 20-GiB worker/12-GiB reserve. The Ward trace
join and useful signed derivative/scaling estimate remain separate.

Actual consumer extension: choose the produced square weight
W=Vbar^2*Gout_l^2 and transport the last transfer outputs to the exact
existing `exactScoreAngularBudget`. Preserve every active signed row in
the finite sum, rather than replacing it by an active-count ceiling.
Incoming k and outgoing l remain independent; the existing scalar
(1+sigma)>=0 is the only additional guard. This is a direct SAME-action
consumer, not a new analytic budget assumption. Root reviews the appended
transport/sum proof and rechecks this same leaf narrowly.

## Observed matched marginal and finite Ward estimate (2026-10-08 UTC)

Classification: VERIFIED PROGRESS, no broad chart closure. The actual
positive terminal density is q*a on LOWER coordinates, not q*lift(a).
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean`
now constructs its certificate, output independence and full-action pin;
`terminal_momentD_pin:455`, `terminal_momentG_pin:465` and
`terminal_local_signed_score_bound:649` retain the actual A=Ta first/all
nine ordered second jets. The final inequality is exactly the selected
matched Gram below, for supported lower phi and frozen output u.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRatioRefinement.lean`:
`original_lastStep_incomingRatio_score_reconstruction_le:282` now keeps
(1+eta)*H[W*S0^2] with S0=score(A,T(a*phi_k)); its original finite incoming
error payment is unchanged. The old `original_lastStep_incomingRatio_score_square_le:357`
retains its statement and follows by the coarse noise cap applied separately.
This supplies a signed-preserving leading consumer, unlike using the old
already-capped theorem as though its leading Hessian survived.

`lean/YMGap/Continuum/QuaternionHaarFiniteReciprocalHessianSign.lean`:
`reciprocal_multiplier_derivative_pin:63`,
`finite_reciprocal_favorable_certificate:95`,
`finite_reciprocal_hessian_ibp_le:179` prove the exact successor slope,
constructed favorable correction and weighted Hessian upper bound in one
fixed angular plane. Root and independent reviewer verified remainder
sign, successor index, factor TWO and k=0/constant-A tests. The retained
J(F) is literal, not bounded or discarded.

Final focused logs (only these scopes are claimed):

| Target | Final log | Printed gates |
| --- | --- | --- |
| LocalMarginalJets helper exports and old proofs | `/private/tmp/ym-local-marginal-api-20261008a.log` | 15 |
| TerminalLocalSignedGram | `/private/tmp/ym-terminal-local-gram-20261008c.log` | 10 |
| LastStepRatioRefinement, including old consumers | `/private/tmp/ym-score-reconstruction-retained-20261008b.log` | 8 |
| FiniteReciprocalHessianSign | `/private/tmp/ym-finite-reciprocal-hessian-20261008b.log` | 3 |

All printed dependencies are exactly {propext, Quot.sound}; no source
sorry, new axiom, classical/native shortcut or frontier-field weakening.
Initial namespace/definitional-inference and syntax errors were repaired,
not used as evidence; no option/limit was increased. Full-source root
review and independent mathematical reviews found no substantive defect.
Each compiler launch had a fresh process/memory/swap preflight, one
20-GiB worker and 12-GiB reserve, 87--88% free and zero swap. All checks
finished in their initial tool calls; no competing compiler process was
observed. Root imports registered only, no full build/audit/guard or baseline
refresh.

Checked-source SHA256, in the target order above:

```text
0f3422675902cbc5c36c01936e960284af094ec5860fe57e358b7f8ae3f02898
71b90d324aeef1e16914ffb2b095d98ba1c00400333ba197af96a74fb2bbfded
49ce0dc704023d9a4869f00f12761df0a92ea2f79417f27e7feee7e95e8a8975
3943cea591aec2756fd71cd6f1acd7f1629a6886b51b61e6fa295cc75807c97f
```

Decision: CONTINUE through actual SIX-plane reconstruction / THREE paired
Gram assembly and the Ward trace join. Then the analytic residue is the
signed derivative of the ACTUAL F=Vbar^2*N, incoming approximation errors
and BOTH signed Taylor remainders relative to SAME surviving form on a
justified scaling family. No noise-to-surviving-square bound is adopted.
The matched Gram and one-plane Ward estimate do not supply that residue.
All scaling, survival, completed OS, physical time/volume, full SAME QFT,
every compact simple group and Clay claims remain OPEN. Canonical chart
unchanged, no reprint.

The latest pasted lattice-measurement note has been re-read and independently
reconciled with the existing calibration audit/work-plan guard; no additional
correction or usable theorem input was found. No repeated literature scan,
paper list, numerical mass premise or stronger quantum Sobolev assumption.

## Selected estimate: favorable finite reciprocal correction (2026-10-08 UTC)

Proposition: for the ACTUAL finite reciprocal G=G_(k+1)(A), M=A*G,
and a certified weight F, the exact slope is
J(M)=scale(upper)*(k+1)*residual(remainder(A),k)*J(A).
The upper-window certificate produces G>=0 and residual>=0, so
F*G*J(A)*J(M) has a square certificate. In the weighted Haar identity

```text
H[F*G^2*(A*J^2(A)-J(A)^2)]
 = -H[A*G^2*J(A)*J(F)] - 2*H[F*G*J(A)*J(M)],
```

only the LAST term may therefore be discarded in an upper bound.
The actual Gram consumer uses F=Vbar^2*N. J(F) remains signed and
unbounded; this is not the refuted generic weighted-Hessian sign claim.
For three constant paired directions the leading cost occurs THREE times.
No variable-direction derivative is silently omitted.

Available inputs: literal reciprocal cancellation, successor residual
derivative, produced upper-window reciprocal/residual certificates and
angular Haar IBP on the same carrier. Test k=0 (G=scale), constant A,
F=0 and the sign convention remainder=scale*A-1. Abandon if the sign
requires an exact inverse, a Hessian premise or noise bounded by the
surviving square. The implementation starts with one fixed angular plane;
paired-direction consumption needs its own exact join.

Independent reviewer owns one bounded leaf; root reviews full source and
alone runs a narrow monitored check, one 20-GiB worker, 12-GiB reserve,
fresh capacity preflight. No broad build/audit/guard. Useful control of
J(Vbar^2*N), incoming errors and both Taylor remainders on the SAME
scaling trajectory remains OPEN.

## Selected next experiment: matched positive terminal law (2026-10-08 UTC)

Proposition: keep the produced positive LOWER terminal a in q_a=q*a,
so I(q_a*P)=A=T(a), with P the unchanged selected original output heat
packet. For a supported lower polynomial phi put b=T(a*phi),
N=A*T(a*phi^2)-b^2. Produce

```text
H[R*firstJet(u,pairedScorePlus(A,b))^2]
 <= H[R*N*(C*threeSquare(u)*A^2 + A*frozenDD_u(A)-frozenD_u(A)^2)].
```

Consumer: the literal incoming-ratio score payment and its exact outgoing
Vbar^2*G_A^2 weight, not a T1-based reciprocal. Inputs: existing terminal
certificate/support, local q/action/output-independence, original heat
curvature/windows, head differential commutation, conditional_signed_score_bound,
and actual transfer integration. Minimal algebraic API exports may avoid
duplicating the T1 proof; preserve all existing public statements. No new
analytic positivity, derivative, inverse or sign premise is allowed.

Prediction/tests: phi=0 or constant gives N=score=0; u=0; every ordered
second jet; selected output versus lower a; identical original action and
partitions. Actual arbitrary c still needs its supplied finite reciprocal
approximation/error payment, NOT an exact c/a assertion. Revise if the law
silently puts a on the output, drops an action factor, requires stronger
analytic inputs, or merely returns an unrelated Gram.

Sol owns bounded implementation and minimal reused-helper exports;
independent read-only review studies complete signed noise/spatial derivatives
and finite multiplier A*G_A-1. Root inspects full sources and alone compiles
serialized narrow targets, one 20-GiB worker and 12-GiB reserve with fresh
dynamic preflights. No broad build/audit/guard, limit rise, numerical oracle
or routine literature scan. The useful combined bound in SAME surviving
form/scaling units remains a separate analytic producer, not promised by
this selected finite join.

## Observed actual original marginal jets (2026-10-08 UTC)

Classification: VERIFIED PROGRESS. For T1=I(W), the SAME-action local
moments now satisfy coefficient-exact identities

```text
D = firstJet(u,J(T1));
G = quadraticForm(u,J_i(J_j(T1))) + C*threeSquare(u)*T1;
T1*G-D^2 = T1*frozenDD(T1) + C*threeSquare(u)*T1^2 - frozenD(T1)^2.
```

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalMarginalJets.lean`:
`frozenMarginalFirst:70`, `frozenMarginalSecond:74`,
`local_momentD_pin:464`, `local_momentG_pin:473`,
`localSignedFisher_marginal_pin:497`, `lastStep_local_differential_gram:516`.
All nine ordered jets remain, u is not differentiated, and q's independence
and original action factor pin are produced. The final differential Gram
uses the unchanged hypotheses and literal original residual/noise. No
analytic upper bound on its right side has been asserted.

Final focused log `/private/tmp/ym-local-marginal-jets-20261008d.log` PASS;
six printed gates exactly {propext, Quot.sound}. Checked-source SHA256:
`089d1d16ae040fd44354a86eb9aa6eb5153f76108a6ba717c29d8850f2a9b0c4`.
Independent read-only review found no substantive defect in the ordered
commutations, factor orientation or cost pull-through; root inspected the
complete source and direct Gram consumer. Initial namespace/coefficient
type errors and one deterministic implicit-inference timeout were repaired
with explicit typed intermediates, not increased limits. Failed-check
sorryAx output is not evidence; the final source introduces no sorry/axiom.
Every launch used a fresh dynamic preflight, one 20-GiB worker and a 12-GiB
reserve; 87--88% free memory and zero swap. Root import registered only;
no full-root/tree build, audit, guard or baseline refresh.

Decision: CONTINUE to the marginal/weight alignment and combined signed
estimate described below. Scaling/survival/completed OS/physical/QFT/
every-group/Clay remain OPEN. Broad chart unchanged, no reprint.

## Selected finite join: actual original marginal jets (2026-10-08 UTC)

Proposition: identify the produced local D/G with frozen first and all nine
ordered second paired derivatives of the ORIGINAL T1. Consumer:
`BF4ExactSlabFixedSpatialLocalSignedGram.lastStep_local_signed_gram`; its
signed Fisher is then an actual differential expression, not unrelated jet
data. Inputs: produced localOutputDensity independence and q*P=W, original
action integral pin, twice head-derivative commutation, and lifted-coefficient
pull-through. No new analytic hypothesis is needed for these identities.

Prediction/tests: D=firstJet(u,J(T1)); G=quadraticForm(u,J_i(J_j(T1)))+
C*threeSquare(u)*T1, including zero/constant u and every ordered i,j. Revise
if u is differentiated, a jet is symmetrized or T1 is replaced by Ta/free
heat. Sol owns one leaf; root inspects it and serializes a focused check with
one 20-GiB worker, 12-GiB reserve and a fresh dynamic preflight; independent
read-only mathematical review runs in parallel. No broad build/audit.

Next analytic decision: weighted Haar IBP retains a negative square but
also derivatives of the literal spatial/reciprocal/noise weights and u.
Positivity/windows alone do not permit dropping that remainder. Control of
the complete SAME signed expression remains OPEN; no integrated Hessian sign
or automatic Taylor cancellation is adopted as a premise.

## Observed weighted-Hessian sign screen (2026-10-08 UTC)

Classification: VERIFIED PRUNING. The literal one-quaternion witness
T=1+x0/2, Q=(1-x0)^2, J=D01+D23 has constructed certificates for Q and
the strict T windows 1/2 and 3/2, but
H[Q*(T*J(J(T))-J(T)^2)]=1/12>0. Therefore positivity/windows alone do
not justify the proposed generic nonpositive integrated-Hessian shortcut.
This is NOT a realization by the original T1 or weight, and does not refute
the complete original signed estimate, a Yang--Mills theory or Clay.

Checked declarations in
`lean/YMGap/Continuum/SU2QuaternionWeightedHessianSignObstruction.lean`:
`witnessWeight_certificate:53`, `witnessTerminal_floor_certificate:59`,
`witnessTerminal_floor_positive:69`, `witnessTerminal_upper_certificate:72`,
`witnessTerminal_first_pin:83`, `witnessTerminal_second_pin:90`,
`weightedHessian_eq_twelfth:101`, `weightedHessian_positive:108`.

Final focused log `/private/tmp/ym-weighted-hessian-obstruction-20261008d.log`
PASS; eight printed gates permitted, the floor's rational positivity gate
axiom-free. Checked-source SHA256:
`bc869bcda43f306acd136935925f71dabc6dbe219f33d8190e73f6a5b2ce7209`.
Root inspected the full source and independently verified the sphere-moment
calculation. Initial namespace/reduction errors and a false raw unpadding
claim were repaired, not used as evidence. Coefficient probes distinguish
[1,0] from [1]: the checked second jet retains its literal trailing zero,
and the Haar congruence then computes the exact compact expression. No
recursion/heartbeat/memory limit, axiom, sorry or trusted oracle was added.
Each check used one monitored 20-GiB worker, 12-GiB reserve and a fresh
process/memory/swap preflight; 87--88% free and zero swap. Root import is
registered, not root-built; no full-tree build/audit/guard or chart closure.

Decision: PRUNE generic sign-dropping; CONTINUE the matched-marginal,
complete signed-weight/error calculation and its still-missing useful
scaling bound. The prior selected experiment/review is retained below.

## Selected sign screen and marginal-alignment review (2026-10-08 UTC)

Decisive finite test: on one quaternion take T=1+x0/2, the paired J01+J23,
and Q=(1-x0)^2. Literal Haar evaluation predicts
H[Q*(T*J(J(T))-J(T)^2)]=1/12>0. The target diagnostic certifies Q as a
square and T's strict half-unit floor if available from the existing
coordinate API. This tests ONLY the proposed generic sign-dropping step:
it does not assert that these polynomials are the original T1/weight.
One small diagnostic leaf, kernel arithmetic, no external numerical oracle,
no broad test run. Abandon the generic sign step if this check succeeds.

Parallel source review narrows the next analytic consumer. The actual score
weight uses the reciprocal of A=Ta, not T1. A positive terminal a can be
retained in the density q*a; its positivity is produced by
`BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_certificate:126`.
This is a PROPOSED marginal-alignment producer, not a checked declaration.
An incoming polynomial reciprocal still needs its actual error payment:
`BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.original_lastStep_incomingRatio_relative_score_le:305`
retains width/nome caps, not uniform scaling control.

The exact matched-reciprocal calculation to preserve (not yet a new Lean
theorem) is, for frozen u and full remaining weight F,

```text
H[F*G^2*(A*DD_u(A)-D_u(A)^2)]
 = -sum_ij H[A*G^2*(J_j A)*J_i(F*u_i*u_j)]
   -2*sum_ij H[F*u_i*u_j*G*(J_j A)*J_i(A*G)].
```

The derivative of G^2 cancels the tempting negative-square bonus. The
finite multiplier A*G is not one; its derivative must remain. Existing
`QuaternionHaarConditionalScoreGradient.reciprocal_score_cleared_derivative:95`
retains this correction. A useful combined bound in the SAME surviving
form is missing. Retain actual spatial/noise/u derivatives and both signed
Taylor remainders; aligning the marginal alone does not pay that budget.

## Observed next experiment: FULL original-action local signed Gram

Classification: VERIFIED PROGRESS (2026-10-08 UTC). The selected local
residual route below now supplies an actual original-action instance, not
only a generic conditional consumer. Put I=partialHaarHeads N, W the literal
halfOpenAction 1, A0=T1, A=Ta, b=Tc, X=lift(A)*c-lift(b)*a. At a selected
active output slot s, use the paired frame at N+s and frozen lifted output
coefficients u. Then

```text
P=heatAt(N+s,s), q=remaining kinetic factors*(spatialWeight*liftN(1));
q*P = W, I(W*X)=0;
d=sum_i liftN(u_i)*J_i(P);
ddAug=sum_ij liftN(u_i)*liftN(u_j)*J_i(J_j(P)) + C*|liftN(u)|^2*P;
D=I(q*d), G=I(q*ddAug), V=I(W*X^2);
score=sum_i u_i*(A*J_i(b)-b*J_i(A));
H_N(R*A0*score^2) <= H_N(R*V*(A0*G-D^2)).
```

The selected packet is reversed ONLY by the checked coefficient symmetry.
The entire direction, all first and all nine ordered second jets travel
through the same explicit pair chart. The reverse certificate uses supported
Haar-carrier inverse transport, not raw coefficient equality of padded caps.
The same `prefixCurvatureCost(w)` and `prefixFrozenCurvatureCutoff(w)` are
retained. No dimension, volume, direction or inverse-floor loss enters the
cost; its nome dependence is explicit, NOT a near-one/scaling-uniform claim.

The full density is produced positive at the original head cutoff. Its
selected-output independence uses the original active-list nodup, and its
coefficient-exact reconstruction preserves every other kinetic factor, the
complete spatial weight and lifted unit. Arbitrary lower-supported a,c need
no positivity or quotient representation. The existing actual mean-zero pin
supplies the determinant specialization, without an extra marginal multiplier.
R has only its certificate, no support/independence premise. Zero and
proportional sources are admitted; no strict noise hypothesis is used.

### Exact checked declarations and verification boundary

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `pairedDerivativeAt_supported/carrier`, `chain_pairedDerivativeAt`, `chain_pairedSecondAt` | `lean/YMGap/Continuum/SU2QuaternionPairedFrameAt.lean:59`, `:71`, `:105`, `:126` | `/private/tmp/ym-paired-frame-at-20261008c.log` |
| `frozenCurvatureAt_supported`, `chain_frozenCurvatureAt`, `heatAt_frozen_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatAtFrozenCurvature.lean:72`, `:116`, `:170` | `/private/tmp/ym-paired-heat-at-curvature-20261008b.log` |
| `zero_mean_momentDeterminant_pin`, `conditional_zero_mean_signed_score_bound` | `lean/YMGap/Continuum/SU2QuaternionConditionalZeroMeanSignedGram.lean:39`, `:96` | `/private/tmp/ym-zero-mean-gram-20261008.log` |
| `lastStepAction`, `action_integral_pin`, `plane_score_integral_pin`, `paired_score_integral_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPairedScorePin.lean:54`, `:58`, `:122`, `:159` | `/private/tmp/ym-last-step-paired-score-20261008c.log` |
| `localOutputDensity_supported/certificate/independent/action_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalOutputDensity.lean:69`, `:79`, `:89`, `:102` | `/private/tmp/ym-local-output-density-20261008.log` |
| `local_paired_score_integral_pin`, `local_frozen_score_integral_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalPairedScorePin.lean:139`, `:196` | `/private/tmp/ym-local-paired-score-20261008b.log` |
| `lastStep_local_signed_gram` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalSignedGram.lean:114` | `/private/tmp/ym-local-signed-gram-20261008c.log` |

Seven final focused targets/22 printed gates, all within {propext, Quot.sound}.
Root inspected complete final sources; independent mathematical review found
no substantive defect. No source sorry/custom axiom/classical/native shortcut,
frontier weakening or baseline refresh. Early checks failed missing namespace
opens, an incompletely rewritten chart product, a misassociated transitivity
chain and unfolding of large action definitions. Local irreducibility of the
existing action factors resolved the deterministic heartbeat timeout without
raising memory or heartbeat limits. Failed-check outputs are not evidence.

Every launch had a fresh dynamic process/memory/swap preflight. One capped
20-GiB worker, 12-GiB reserve, 87--88% free and zero swap; all checks finished
in their initial calls. Root imports are registered, NOT root-built. No
full-tree audit/build/guard or broad chart closure was run/claimed.

Final checked-source SHA256:

- `SU2QuaternionPairedFrameAt.lean`: `bde06a8062e1b83ce367b36d02a4afad40e8b54e9f0c9f1a15c7b40d15e24b8f`
- `SU2QuaternionPairedHeatAtFrozenCurvature.lean`: `c58f0c2e3fb2d3203d210b1ef30a71e8354cb9c1c4f0e8b944bf1623e5307e92`
- `SU2QuaternionConditionalZeroMeanSignedGram.lean`: `5bbc4b3d0e922f579d3f88ce8a697167ce8c891cba32b6088ddecb3aec5abcfb`
- `BF4ExactSlabFixedSpatialLastStepPairedScorePin.lean`: `dcb128c072a64a483df6c2d513ff0bb2f26cf3187d5cd186dadd57d84fde42e6`
- `BF4ExactSlabFixedSpatialLocalOutputDensity.lean`: `4dbb76ac287d19004b88385357fd7b02015566397a85b4d46639175a7371b217`
- `BF4ExactSlabFixedSpatialLocalPairedScorePin.lean`: `ee0b8127fb300b2203cb3f2611b5723be34f5e7e1e32384636836ebfa3668317`
- `BF4ExactSlabFixedSpatialLocalSignedGram.lean`: `b834092ba717df62aeecc11b3eef87568069b14f4292bb107fa6771b86a19925`

### Decision: continue, with a smaller finite residue and an OPEN analytic one

The action, source score and arbitrary-block curvature join selected below
is now constructed. D/G remain PRECOMPUTED local jet moments; no declaration
in this increment pins them to frozen derivatives of T1. The next finite
producer should prove D=firstJet(u,J(T1)) and
G=quadraticForm(u,J_i(J_j(T1)))+C*threeSquare(u)*T1. Existing output
independence, exact action pin, head-derivative commutation (twice) and
lifted-coefficient pull-through supply the inputs. This is NOT the square of
a variable-coefficient vector field, which would differentiate u.

Then the genuinely missing estimate is useful control of the SAME signed
Fisher/noise expression in the existing exact-score budget, with its actual
source/error, width, cutoff and scaling parameters. The Gram does not
produce that control or an every-state gap. The marginal is T1, NOT Ta.
Independent survival, completed OS, physical time/volume, SAME limiting QFT,
every compact simple group and Clay remain OPEN. The canonical displayed
claims did not change, so there is no chart reprint.

## Selected next experiment: original centered residual, local output frame

Decision (2026-10-08 UTC): use the already constructed paired residual
X=lift(Ta)*c-lift(Tc)*a under the FULL one-step action W, rather than
requiring a representation c=a*phi. Its existing head-integral mean is zero.
The three-moment determinant therefore predicts the sharper cleared bound

```text
T1*S^2 <= I(W*X^2) * (T1*G-D^2),
T1=I(W), D=I(frozen first output jet of W),
G=I(frozen second output jet of W + C*threeSquare(u)*W).
```

The mean-zero specialization uses `conditional_determinant_nonnegative`,
not the centered-score consumer that would add another marginal multiplier.
The existing mean and square pins are in
`BF4ExactSlabFixedSpatialLastStepScoreVariance`; its local mixed score pin
is to be exposed for the actual paired output frame. This preserves arbitrary
lower-supported a,c, with no positivity or quotient premise on either source.

Root's remaining experiment is to expose heatAt(s,N+s) as a local factor,
recode the produced original-prefix curvature to OUTPUT block N+s, and
retain all other kinetic factors, the spatial action, and the literal lifted
unit in q. Existing factor selection, certificates and output independence
are available; no whole-product tensorization is required for this local
bound. Frozen coefficients stay outside differentiation. The signed Hessian
is that of T1, NOT Ta, and stays an integrated correction rather than an
assumed nonpositive input.

Decisive tests: a=0 or c=0; proportional sources; constant frozen direction;
all nine ordered jets; unique selected active factor; correct output block;
literal halfOpenAction normalization. Revise if q still depends on that
output block, if a derivative acts on frozen coefficients, or if the action
or its unit padding is silently replaced. Verify only focused leaves with
one capped 20-GiB worker and a fresh dynamic preflight at each launch.
Sol implements the two bounded algebra/score pins in parallel; root retains
source review and serialized compilation. This is a selected finite
experiment, NOT a proved full-action bound or OS/scaling/Clay closure.

The user's lattice-measurement note is already reconciled in
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and the live plan. No new
numerical premise or research branch is needed: the local estimate must still
meet SAME-operator OS reconstruction, physical time and all-state control.

## Observed three-replica signed conditional jet Gram (2026-10-08 UTC)

Decision: pursue the polynomial-valued conditional join directly. A rational
full-Haar centered Schur bound would not itself cancel a surviving polynomial
marginal. The chosen proposition is arbitrary-certified-insertion positivity
of the SAME conditional determinant N*F-S^2, with the signed Hessian retained.
Available inputs: produced original-prefix frozen curvature; positive kernel
windows; shared-tail copy/lift/head-Fubini certificates; constructive integrated
positive-window reflection. No finite certificate-level division is assumed.

Classification: VERIFIED PROGRESS. For three copied rows with
kernel P_i, score d_i, augmented Hessian dd_i and observable f_i, put
h_i=f_j-f_k cyclically, B_i=P_j*P_k and w=sum_i B_i*d_i*h_i. The cleared
replica determinant satisfies

```text
(P0*P1*P2)*T = w^2 + sum_i (B_i*h_i)^2*(P_i*dd_i-d_i^2).
```

All three curvature witnesses construct the right side. Kernel windows
cancel the product multiplier only in Haar order. Exact shared-tail triple
integration now identifies the weighted T with six times the 3x3 moment determinant.
Multiplying the retained positive marginal A gives N*F-S^2=A*det(M), without
a polynomial marginal inverse or a strict variance premise. This is an
integrated order claim under arbitrary certified tail insertions, not a claim
that T or the divided determinant has a finite square certificate.

Pre-verification checks and revision criteria (retained experiment record):
constant/zero observable, zero heads/tail, nonzero score mean,
signed cross terms and exact factor SIX; preserve the actual input action in
each copy and all shared survivors. Verify narrow leaves serially with one
20-GiB worker/fresh dynamic preflight, no full audit. Revise if replica copies
share an integrated head, an insertion is lost, positivity is assumed for the
target determinant, or an actual positive-kernel window is unavailable. The
remaining original product/domain-jet recoding and incoming-source residual
must still meet this producer; no OS/scaling/Clay claim changes.

### Constructed output and its exact boundary

With I the ORIGINAL ordered-head integral, define A=I(qP), b=I(qP*phi),
D=I(qd), v=I(qP*phi^2), e=I(qd*phi), G=I(qddAug). The checked output is

```text
N=A*v-b^2, S=A*e-b*D, F=A*G-D^2;
H_tail(R*S^2) <= H_tail(R*N*F).
```

The input density q and tail insertion R have explicit square certificates;
R has NO support or independence premise. The actual marginal A is produced
positive by head integration and retained as a spectator. Neither A nor N
is assumed strictly positive or inverted. Copies of constant caps are
identified only by supported Haar-carrier equality, not false raw coefficient
equality. The exact factor SIX is cancelled as a positive rational, not an
analytic loss. Zero heads/source and constant observables are admitted by
the general statements; independent source review checked these boundaries.

The literal ORIGINAL-prefix consumer constructs its curvature and windows
from the prior producers, with ddAug=dd+C*threeSquare(u)*P and the named
fixed-nome onset. No Hessian sign, curvature bound or target Gram inequality
is a premise of that consumer. The polynomial cost stays INSIDE G.
The precomputed paired-jet moments D/G are NOT identified with derivatives
of the marginal A when q or coefficients depend on integrated heads. This
is an actual finite conditional jet-moment inequality, not yet the full
interacting-action score estimate or an arbitrary incoming c=q*phi claim.

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `cleared_replica_pin`, `cleared_replica_certificate`, `centered_difference_pin` | `lean/YMGap/Continuum/QuaternionHaarClearedThreeGram.lean:89`, `:117`, `:153` | `/private/tmp/ym-cleared-three-gram-20261008.log` |
| `positiveFromLowerWindow`, `multiplyPositiveWindows` | `lean/YMGap/Continuum/QuaternionHaarCertifiedPositiveWindowProduct.lean:44`, `:58` | `/private/tmp/ym-positive-window-product-20261008c.log` |
| `copy_add`, `copy_neg`, `copy_cap_carrier` plus eight unchanged regression gates | `lean/YMGap/Continuum/SU2QuaternionMultiHeadVarianceReplica.lean:320`, `:325`, `:333` | `/private/tmp/ym-copy-cap-20261008.log` |
| `tripleCopy`, `tripleCopy_mul/add/neg/supported/certificate`, `replica_product_three` | `lean/YMGap/Continuum/SU2QuaternionTripleHeadReplica.lean:34`, `:41`, `:60`, `:66`, `:72`, `:95`, `:122` | `/private/tmp/ym-triple-head-20261008c.log` |
| `weighted_replica_integral_pin` (plus `symTensor_integral_pin`) | `lean/YMGap/Continuum/SU2QuaternionConditionalSignedGramReplica.lean:235`, `:144` | `/private/tmp/ym-conditional-gram-replica-20261008.log` |
| `tripleKernelWindow` and its five actual copy/lift producers | `lean/YMGap/Continuum/SU2QuaternionTripleHeadPositiveWindow.lean:195` | `/private/tmp/ym-triple-window-20261008.log` |
| `conditional_determinant_nonnegative`, `conditional_signed_score_bound` | `lean/YMGap/Continuum/SU2QuaternionConditionalSignedGramOrder.lean:127`, `:200` | `/private/tmp/ym-conditional-gram-order-20261008.log` |
| `prefix_cleared_curvature_certificate`, `prefix_conditional_signed_score_bound` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixConditionalGram.lean:49`, `:81` | `/private/tmp/ym-prefix-conditional-gram-20261008b.log` |

Eight final focused targets checked; 35 printed gates within {propext,
Quot.sound}, of which 27 are new and eight are unchanged copy-module
regressions. Root inspected all final sources; independent mathematical
review found no material defect. No source sorry/custom axiom/classical/
native shortcut, weakened field or baseline refresh. Every launch followed
a fresh dynamic preflight; one capped 20-GiB worker/12-GiB reserve, 85--88%
free and zero swap. All checks finished in their initial calls. Root imports
registered, not root-built; no full-tree audit or broad chart closure.

Final checked-source SHA256:

- `QuaternionHaarClearedThreeGram.lean`: `135ae6259a0612f5bdacba975767028e661cd5495ec9d0e0589fb08d18579f04`
- `QuaternionHaarCertifiedPositiveWindowProduct.lean`: `6f7a2038de1a31e0184126435e3ae939085cd8629cce5c9b1b9bdda07d853485`
- `SU2QuaternionMultiHeadVarianceReplica.lean`: `085355d57658e5c281232ae272b467bdc28729c1063f978fafd141819035288b`
- `SU2QuaternionTripleHeadReplica.lean`: `eb686b085c1c54faead901e2e634e8ca1b8150e21f6bc910dae63b9393b1e112`
- `SU2QuaternionConditionalSignedGramReplica.lean`: `1e27690b1e8f0fc4229b2891cc5329aded4915bc25d82d8f7360e5ae488e1566`
- `SU2QuaternionTripleHeadPositiveWindow.lean`: `3b3ef82fc163fa5a79e9a9e45f6fb19ea3e80cc4d750858ccddfe424fb300363`
- `SU2QuaternionConditionalSignedGramOrder.lean`: `c1fc774293f0de15cdd0392aa633676752b92d8d21ffadb96b31e811aa52196d`
- `SU2QuaternionPairedFrozenHeatPrefixConditionalGram.lean`: `fbb8c00a9a0d1f34db0f49237f80d4f54f6a3378944a126377fce2bac9533319`

NEXT: actual product/domain-jet recoding, exact original source/derivative
identifications and incoming reconstruction residual, then useful signed
norm comparison on a justified scaling family. Do not replace this sharper
Gram by historical-noise domination or infer a marginal-derivative pin from
bare integration. The lattice-measurement note remains research context
only, with corrections in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.
All survival/OS/physical/QFT/every-group/Clay obligations remain OPEN.

## Observed signed integrated ORIGINAL-prefix Gram (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS, without asserting an integrated Hessian sign.
The existing positive-window order reflection completes the square on the
SAME kernel/background, removes its actual positive kernel multiplier, and
retains the second-jet correction in the discriminant. The unchanged
sign-dependent theorem remains intact; its stronger signed precursor is now
public and consumed by the produced full original-prefix curvature.

For p=pairedPrefix(w,K), d=sum_i u_i*Ji(p), dd=sum_ij u_i*u_j*JiJj(p),
R=sum_i u_i^2 and C=prefixCurvatureCost(w), the ACTUAL consumer proves

```text
H(background*d*f)^2 <= H(background*p*f^2) * H(background*(dd+C*R*p)).
```

For polynomial u, R is kept INSIDE integration, never pulled out as a scalar.
Coefficients are frozen; all nine mixed jets remain actual. The actual
prefix floor gives lower window m, and the produced interval enlarged to
prefixValueCap+m gives the upper window. Its positivity/order is proved.
The exact zero-lambda curvature pin consumes the checked prefix certificate.
No curvature or nonpositive-Hessian premise is supplied by the caller.
The background certificate and supported test ARE explicit premises.
This is full Haar, not a construction of the original normalized partial
conditional law or an instantiation of its complete interacting action.

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `curvature_signed_dual_bound` (plus unchanged `curvature_dual_bound` regression gate) | `lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:180`, `:148` | `/private/tmp/ym-oct7-signed-curvature-dual1.log` |
| `prefix_augmented_curvature_pin`, `prefix_signed_gram_bound` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixSignedGram.lean:60`, `:89` | `/private/tmp/ym-oct7-original-frozen-signed-gram2.log` |

Two further focused checks/four printed gates within {propext, Quot.sound},
including the unchanged dual theorem. Root inspected the final source;
independent read-only scope review found no material defect. No source
sorry/new axiom/classical/native shortcut, field weakening or baseline
refresh. Fresh dynamic preflights, one 20-GiB worker, 12-GiB reserve,
87% free and zero swap. Root import registered, not root-built; no full-root/
tree audit or broad chart change. Final checked-source SHA256:

- `QuaternionHaarCurvatureDualBound.lean`: `a2f1b05a20a2b636c3d14787b532024f5496548e3da96da9e595dbb86cadab49`
- `SU2QuaternionPairedFrozenHeatPrefixSignedGram.lean`: `f58a4ff26e09716c0ed1192841d728ea43aac8f104e62e1fd3746011b058e8d6`

NEXT recode actual pairs/products as needed and assemble the original
conditional centered Gram, retaining A*F2(A)-F1(A)^2 rather than demanding
F2(A)<=0. The genuine source law/error join, coefficients pulling through
head integration and cancellation of the ACTUAL positive marginal are
still required. For arbitrary c, no silent phi=c/a. A permutation alone
also does not expose a four-link plaquette word as a two-block scalar.
All useful scaling, independent survival, completed OS, physical/volume,
SAME QFT, every group and Clay remain OPEN. No chart reprint.

## Observed full ORIGINAL-prefix frozen matrix (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS, beyond the weighted finite matrix.
The user lattice-measurement note remains research context only, with the
corrections in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.
No channel measurement or finite-spacing Hamiltonian equality is a premise.

### Mathematical contraction

Write p for the ORIGINAL K-th prefix, f for the literal K+1 weighted heat,
e for its K+1 deficit and R=sum_i u_i^2. EVERY first/mixed jet is actually
differentiated before multiplying the supported polynomial coefficients u.
No derivative acts on u. The literal signed entry discrepancy is

```text
M_ij = delta_ij*C*(2*p*e-e^2)
       + p*e_ij + e*p_ij - e*e_ij
       - p_i*e_j - e_i*p_j + e_i*e_j.
curv_C(p,u)-curv_C(f,u) = sum_ij u_i*u_j*M_ij.
```

Both cross terms are retained individually, not replaced entrywise by a
symmetrized expression. No Hessian symmetry is assumed. Actual caps
U0,U1,U2 and epsilon,2*epsilon,4*epsilon construct intervals for every M_ij
with the existing scalar errorCap E. A thin three-slot adapter zero-pads
the coefficient vector into the existing six-column envelope, yielding
the PLUS certificate 6*E*R+sum_ij u_i*u_j*M_ij. Dummy matrix cells reuse
M_00; their coefficientwise-zero rows/columns contribute nothing.

Fix Cbar and the original caps BEFORE choosing epsilon. Use the existing
`errorTolerance` at precision floor m/4, m=headFloor(w). Its proved budget
gives E<=(m/4)^2, hence 6*E<=3*m^2/8<=m^2. The actual original floor
constructs p^2-6*E. Multiplication by the supported-square certificate for
R and addition to weighted curvature plus discrepancy yields curv_(C+1)(p,u).
Raising C to its fixed-nome Cbar gives cost `prefixCurvatureCost(w)`.
Factor six and the floor affect precision/onset, not this cost. No global
coefficient bound, endpoint division, inverse-floor multiplier, direction,
cutoff or carrier-size penalty. Nome dependence remains explicit.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `paired_mixed_expansion`, `mixedInterval`, `prefix_mixed_split_pin`, `deficit_mixed_interval`, `prefix_mixed_interval` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixMixedDeficit.lean:101`, `:121`, `:136`, `:144`, `:161` | `/private/tmp/ym-oct7-mixed-prefix1.log` |
| `three_polynomial_matrix_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarThreePolynomialMatrixEnvelope.lean:142` | `/private/tmp/ym-oct7-three-matrix4.log` |
| `curvature_difference_pin`, `error_interval`, `curvature_approximation_certificate` | `lean/YMGap/Continuum/QuaternionHaarFrozenCurvatureApproximation.lean:113`, `:141`, `:180` | `/private/tmp/ym-oct7-frozen-approx2.log` |
| `prefixFrozenCurvatureTolerance`, `prefixFrozenCurvatureCutoff`, `prefix_frozen_curvature_adaptive_certificate`, `prefix_frozen_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:48`, `:53`, `:88`, `:127` | `/private/tmp/ym-oct7-original-frozen-curvature2.log` |

Four focused leaves/16 printed gates within {propext, Quot.sound}; three
printed data definitions axiom-free. Root inspected the final sources;
independent read-only review found no material defect in the exact K+1
objects, mixed order/signs, homogeneous payment or noncircular cost.
No source sorry, custom axiom, classical/native shortcut, field weakening
or baseline refresh. One capped 20-GiB worker, 12-GiB OS reserve, fresh
dynamic preflight before every compiler; 87--88% free, zero swap. Checks
finished in their initial calls. Root imports registered, not root-built;
no full-root/tree audit or broad chart closure.

Final checked-source SHA256:

- `SU2QuaternionPairedHeatPrefixMixedDeficit.lean`: `5bee092980f1de35693465eb6a03bc080ed9503b23ca080cc4c403e401f8baa6`
- `QuaternionHaarThreePolynomialMatrixEnvelope.lean`: `579a7a143de8f47dfa6990d47da1a2b167772eba3d60d23c54500ee5a15070ef`
- `QuaternionHaarFrozenCurvatureApproximation.lean`: `def545b6282a980dd1664e106dd71a2f5b55f452919b861f48f99df737363c87`
- `SU2QuaternionPairedFrozenHeatPrefixCurvature.lean`: `b278fc6c7170c4d2e402857ed28ff9305e1eeb6590eacaf73b2c12f5c449bc25`

### Next actual consumer

Establish arbitrary-block/product recoding as needed, then the ORIGINAL
interacting conditional signed Gram/Hessian join. The actual integrated
second-jet sign required by `curvature_dual_bound`
(`lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:148`) is not
supplied by a free heat marginal or positivity alone. Keep every original
action factor and signed correction. No new assumed-estimate wrapper.
Useful scaling, independent survival, completed OS, physical/volume control,
SAME QFT, every compact simple group and Clay remain OPEN. Broad chart
unchanged; no reprint. Earlier sections retain their checkpoint boundaries.

## Observed full frozen weighted-heat matrix (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS, beyond separate basis-direction bounds.
Use arbitrary supported polynomial u:Fin 3->RatPoly, R=threeSquare(u),
s=frozenFirstJet(u,X). The coefficients multiply the actual jets AFTER
differentiation; no derivative acts on u. The existing
`SU2QuaternionPairedFrameScalarJets.frozenScalarSecondJet_pin`
(`lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:211`)
already supplies the full scalar acceleration -R*X. It is reused, not assumed.

### Mathematical contraction

The actual first jets and norm relation give

```text
R*(1-X^2)-s^2 = sum_i (u cross relativeVector)_i^2.
```

Each square has original finite support and constructs a Certificate.
The mixed chain rule computes EVERY ordered JiJj before frozen contraction:

```text
frozenFirstJet(u,h) = h_x*s,
frozenSecondJet(u,h) = h_xx*s^2-h_x*R*X.
```

Both derivatives are pinned on the literal shifted finite Jacobi heat,
not independently assigned jets. The final coefficient contraction is

```text
C*R*h^2 + h*frozenSecondJet(u,h) - frozenFirstJet(u,h)^2
  = R*radial_C(h) + [R*(1-X^2)-s^2]*(h_x^2-h*h_xx).
```

The two right-hand products have constructed certificates on shared
variables. Cost C=radialCap(w,N)+delta is unchanged, with N>=1, the actual
omitted-factor onset and delta>0. No coefficient magnitude bound, unit
direction, positive direction norm, endpoint division or dimension penalty.
This is a frozen quadratic form, NOT the square of a variable-coefficient
differential operator. Scope is the WEIGHTED finite heat on original blocks
zero/one; full original-prefix matrix transport is still OPEN.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `frozen_complement_pin`, `frozen_complement_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenComplement.lean:179`, `:216` | `/private/tmp/ym-oct7-frozen-complement2.log` |
| `paired_subst_mixed`, `frozen_subst_first`, `frozen_subst_second` | `lean/YMGap/Continuum/QPolyHaarFrozenChain.lean:33`, `:99`, `:111` | `/private/tmp/ym-oct7-frozen-chain2.log` |
| `frozenHeat_first_pin`, `frozenHeat_second_pin`, `frozen_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenJacobiCurvature.lean:47`, `:54`, `:83` | `/private/tmp/ym-oct7-frozen-jacobi-curvature1.log` |

Three focused leaves/11 printed gates pass within {propext, Quot.sound}.
Root read final source; independent mathematics/source review found no
defect in ordered jets, frozen coefficient handling, normalization or the
cost. No source sorry, custom axiom, classical/native shortcut, field
weakening or baseline refresh. Fresh process/memory/swap preflight before
every compiler, one 20-GiB worker and 12-GiB reserve; 87--88% free and zero
swap observed. Final checks finished in the initial call. Root imports
registered, not root-built; no full-root/tree audit or broad chart closure.

Final checked-source SHA256:

- `SU2QuaternionPairedFrozenComplement.lean`: `cc5fcdd443f84a48aae5a3da0b9d90a25c859f5487f353abf0c00e1d2a0d815d`
- `QPolyHaarFrozenChain.lean`: `a74a8b1896bb23db28a4363c9d92d0b3c0c088f61ac867fe8b75d8ab33ee9bd7`
- `SU2QuaternionPairedFrozenJacobiCurvature.lean`: `a40cd07ad07cec5d115a77bdd9332d898668bdaac2a3111eb5b05c972c3dde04`

### Next actual consumer

Transport this full matrix to the original prefix with ordered paired
mixed deficit entries. Reuse
`QuaternionHaarSixPolynomialMatrixEnvelope.six_polynomial_matrix_envelope_certificate`
(`lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:134`).
Its three-slot zero padding still pays SIX times the entry cap; do not infer
entryCap*R. This conservative factor can be paid in precision/onset ONLY.
The existing public two-column producer at :74 also permits a factor-three
version by summing nine ordered pairs, but is not a necessary extra compiler.
Do not cap the coefficient polynomials globally or erase the mixed signs.
Then establish arbitrary-block recoding as needed and the ORIGINAL
interacting conditional sign estimate. These estimates and all scaling,
survival, OS, physical/volume, SAME QFT, every-group and Clay requirements
remain OPEN. Broad chart claims are unchanged; no chart reprint.

## Observed ORIGINAL-prefix paired curvature (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS. The actual weighted heat now meets the
ORIGINAL unweighted prefix through produced value and paired-jet errors.
The user lattice-measurement note remains context only, with the corrections
in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. No measured channel
mass, finite-spacing Hamiltonian identification or continuum regularity is
assumed. Earlier sections below retain their checkpoint-time boundaries.

### Mathematical contraction

Let p be the original heat prefix, f the literal K+1 weighted heat, and e=p-f.
All first/second jets below are the ACTUAL paired derivatives. The proved
coefficient identity is

```text
curv_C(p)-curv_C(f)
  = C*(2*p*e-e^2) + p*dde + e*ddp - e*dde - 2*dp*de + de^2.
```

Original jet caps U0,U1,U2 and deficit caps a,b,c yield the constructed
shared-variable interval cap

```text
E = C*(2*(U0*a)+a*a) + ((U0*c+a*U2)+a*c) + (2*(U1*b)+b*b).
```

Set a=epsilon, b=2*epsilon, c=4*epsilon. First fix
Cbar=C_T(w)+geoTailBase(4,w*w,0)+1, which dominates C=radialCap(w,K+1)+1
at EVERY cutoff. Set B=Cbar*(2*U0+1)+4*U0+U2+4*U1+8 and
epsilon=divPos(m*m,B+1+m*m), m=headFloor(w). Positive denominator,
positive epsilon, epsilon<=1 and epsilon*B<=m*m are proved. The retained
nonnegative identity

```text
epsilon*B-E
  = (Cbar-C)*epsilon*(2*U0+epsilon)
      + (Cbar+8)*epsilon*(1-epsilon)
```

pays the full discrepancy. The actual original floor certificate gives p-m;
p+m=(p-m)+2m and
p*p-E=(p-m)*(p+m)+(m*m-E) construct its square payment. Add weighted
curvature, the discrepancy lower certificate and this payment to obtain
original curvature at C+1, then raise it to the fixed cost Cbar+1.
The floor is in epsilon/cutoff ONLY, not an upper-cost denominator.

`prefixCurvatureCutoff(w)` is the max of the original head floor cutoff,
radial onset and actual value/first/mixed deficit cutoffs. The split retains
N=K+1 exactly; the second derivative keeps all four ordered plane terms,
including A*A-A*B-B*A+B*B in the middle paired direction. No invented jet,
weighted-prefix substitution, endpoint division or caller curvature premise.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `prefix_split_pin`, `prefix_first_split_pin`, `prefix_second_split_pin` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixDeficit.lean:203`, `:209`, `:215` | `/private/tmp/ym-oct7-paired-prefix-deficit2.log` |
| `deficit_value_interval`, `deficit_first_interval`, `deficit_second_interval` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixDeficit.lean:222`, `:229`, `:241` | `/private/tmp/ym-oct7-paired-prefix-deficit2.log` |
| `curvature_difference_pin`, `error_interval`, `floor_square_payment`, `curvature_approximation_certificate` | `lean/YMGap/Continuum/QuaternionHaarCurvatureApproximation.lean:72`, `:109`, `:122`, `:151` | `/private/tmp/ym-oct7-curvature-approximation3.log` |
| `curvatureCap`, `errorTolerance`, `error_budget` | `lean/YMGap/Continuum/JacobiHeatPrefixCurvaturePrecision.lean:29`, `:81`, `:175` | `/private/tmp/ym-oct7-curvature-precision1.log` |
| `prefixCurvatureCost`, `prefixCurvatureCutoff`, `prefix_curvature_adaptive_certificate`, `prefix_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixCurvature.lean:44`, `:52`, `:67`, `:101` | `/private/tmp/ym-oct7-paired-prefix-curvature1.log` |

Four focused leaves/37 printed gates pass within {propext, Quot.sound};
eight printed definitions are axiom-free. Root read final source and an
independent read-only review found no material sign, normalization,
same-object, certificate, cutoff or scope defect. No source sorry, custom
axiom, classical/native shortcut, field weakening or baseline refresh.
Every compiler had fresh dynamic process/memory/swap checks, one 20-GiB
worker and a 12-GiB reserve; 87--88% free and zero swap observed. All final
checks finished in the initial call. No concurrent compiler or full-root/
tree audit. Root imports registered, not root-built.

Final checked-source SHA256:

- `SU2QuaternionPairedHeatPrefixDeficit.lean`: `cd4c1fa91c923c8da7c4d73e6d6c04592975baa78ffdb6f11b4ff40ad0e38c13`
- `QuaternionHaarCurvatureApproximation.lean`: `2d24a4dea02bb7364797edda27c6ec3009d47d7040dd86aa8ccbb14e813b042f`
- `JacobiHeatPrefixCurvaturePrecision.lean`: `a4c3e9f0dc153c64a067d75ccff4449f7e882c899a9638c3a6ee5539ab41d686`
- `SU2QuaternionPairedHeatPrefixCurvature.lean`: `9f022be674784a0035e797843e6f49c45839b73c7263eea6bac44dec318b6a66`

### Next actual consumer and unchanged physical boundary

Produce the full frozen-direction matrix and arbitrary-block recoding
where required by the original conditional consumer. The three separate
paired-direction certificates do not bound mixed Hessian terms. Then join
the ORIGINAL interacting conditional score, retaining every action factor
and proving the actual integrated log-Hessian sign, not a free heat identity.
All-vector OS/scaling control, independent continuum survival, physical
calibration/volume/spacing control, SAME QFT, every group and Clay remain
OPEN. The nome is explicit and the cost is NOT uniform as nome approaches
one; 1-w is not an identified physical clock. Broad chart claims remain
unchanged; no chart reprint.

## Observed actual paired-heat curvature join (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS on the SAME finite weighted heat.
The lattice-mass note remains context, not an empirical mass hypothesis.
This increment produces curvature for the literal paired derivatives,
not merely an interface asking for it.

### Mathematical contraction

Let P be the EXISTING finite shifted Euler product and H=P', J=P'', K=P'''.
Appending its actual affine factor F with slope b gives positive polynomial
representatives for V=H^2-P*J, W=H*J-P*K and D=J^2-H*K:

```text
V_next = F^2*V + b^2*P^2,
W_next = F^2*W + 2*b*F*V + 2*b^2*P*H,
D_next = F^2*D + b*F*W + b^2*(H^2+3*V).
```

The actual first THREE formal jets are coefficient-pinned before these
identities are used. Positive shifted coefficients compile D into a Haar
certificate for h'^2-h*h'', where h is the ORIGINAL inverse-nome/half-
normalized finite Jacobi heat. The normalization is squared exactly.
All prefixes, including zero/one, are retained. No heat-floor inverse,
root-interlacing theorem, supplied derivative identity or limit derivative.

For the ACTUAL relative quaternion word on blocks zero/one, X is its scalar.
The three literal paired first derivatives are the NEGATIVE vector
components. Actual norm multiplicativity and the original unit-norm carrier
relation identify 1-X^2-(J_i X)^2 with the OTHER TWO component squares.
This is a constructed certificate under arbitrary original insertion
relations, not an assumed coordinate cone or a division by 1-X^2.

The finite Horner chain rule supplies the actual first and second paired
jets; the second keeps the scalar acceleration term, whose actual value is
-X under the SAME Haar carrier. The final checked polynomial contraction is

```text
C*h^2 + h*(J_i J_i h) - (J_i h)^2
  = radial_C(h)
    + (h'^2-h*h'') * [1-X^2-(J_i X)^2].
```

Both right-hand terms now have constructed certificates. The produced
`paired_curvature_certificate` has C=C_T(w)+tail_N(w)+delta for N>=1,
0<w<1, delta>0 and the existing omitted-factor onset. The floor appears
only in the radial Bernstein construction, NEVER in C. The two scalar
endpoints require no exceptional argument. This is separately for each
of the THREE original plus-paired directions, not yet a full frozen
quadratic-form/matrix estimate.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `angular_subst`, `paired_subst`, `paired_subst_second` | `lean/YMGap/Continuum/QPolyHaarAngularChain.lean:79`, `:149`, `:167` | `/private/tmp/ym-oct7-angular-chain2.log` |
| `product_discriminants_formal_pin`, `discriminants_nonnegative`, `heat_logConcavity_certificate` | `lean/YMGap/Continuum/JacobiHeatLogConcavity.lean:209`, `:313`, `:372` | `/private/tmp/ym-oct7-heat-log-concavity1.log` |
| `paired_first_jet`, `relativeScalarSquare`, `complementSquare` | `lean/YMGap/Continuum/SU2QuaternionPairedScalarSquare.lean:57`, `:76`, `:150` | `/private/tmp/ym-oct7-paired-scalar-square3.log` |
| `radial_substitution_pin` | `lean/YMGap/Continuum/JacobiHeatRadialSubstitutionPin.lean:101` | `/private/tmp/ym-oct7-radial-substitution2.log` |
| `pairedHeat_first_pin`, `pairedHeat_second_pin`, `paired_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedJacobiCurvature.lean:69`, `:77`, `:109` | `/private/tmp/ym-oct7-paired-jacobi-curvature1.log` |

Five focused leaves/25 printed gates pass within {propext, Quot.sound};
four printed data definitions are axiom-free. Root read all final source;
independent reviews checked actual jet signs, normalization, zero prefixes,
carrier padding, endpoint handling and limited scope. No source sorry,
custom axiom, classical/native shortcut, field weakening or baseline refresh.
Every check used a fresh dynamic process/memory/swap preflight, one 20-GiB
worker and a 12-GiB reserve; observed 87--88% free and zero swap. All five
final checks completed at initial observation; no concurrent compiler,
full-root/tree build or audit. Root imports registered, not root-built.

Final checked-source SHA256:

- `QPolyHaarAngularChain.lean`: `36910ac5c324724ecd133a3660d10c22ed621dde115d8c85416eb9371cc6905d`
- `JacobiHeatLogConcavity.lean`: `a12064981d947b6fb85cc4072b2b536c2a1d269dd2de5cc5b95c1286dd5575b8`
- `SU2QuaternionPairedScalarSquare.lean`: `805d403482c884d0d43a0fc1d525e910da6168dafcf608c8786299ab10783a0f`
- `JacobiHeatRadialSubstitutionPin.lean`: `c22e74e641aa8307b2f3e590fa83ffd1350abe200d9d830f91251aa01f022434`
- `SU2QuaternionPairedJacobiCurvature.lean`: `eabb7d006f21a4ea616e136134e6617718fff5e01edc1c20e1e6022715100018`

### Next actual join and unchanged physical boundary

Transfer this curvature, not just a relative absolute derivative budget,
to the ORIGINAL unweighted prefix. Preserve N=K+1 using
`QuaternionHaarAllNomeHeatCertificate.prefix_eq_weighted_add_deficit`
(`lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:65`) and
`JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial`
(`lean/YMGap/Continuum/JacobiWeightedHeatPolynomial.lean:154`). Reuse the
existing value/first/mixed deficit producers named below; a paired second
derivative contains ALL FOUR ordered mixed terms, including the minus signs.
Pay the actual curvature discrepancy with slack using the ORIGINAL
`prefixFloorCertificate` (`lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:137`),
placing its dependence only in precision/onset, not the final upper cost.
These existing dependencies were source-inspected, not recompiled here.

Full frozen-direction curvature, arbitrary-block recoding, original-prefix
curvature transport and the ORIGINAL interacting conditional score remain
OPEN. No integrated log-Hessian sign follows from a free heat marginal.
All-vector OS/scaling estimates, independent nontrivial continuum survival,
volume/spacing control, physical Hamiltonian calibration, SAME QFT,
every compact simple group and Clay remain OPEN. The nome dependence is
explicit; 1-w is not an identified physical clock. Broad displayed claims
stay OPEN and unchanged; no chart reprint.

## Observed general-nome product addition and radial ceiling (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS. Continue the actual original-object route.
The user's measured-mass note remains context only; no channel mass,
finite-spacing Hamiltonian identification or continuum regularity assumption
has been adopted. The earlier checkpoints below retain historical boundaries.

### Mathematical contraction and actual consumer

The product angular jets now have a direct CReal with EXACT original N-th
approximants and `productAngularCutoff(w,epsilon)`, the max of the existing
derivative/prefix cutoffs at epsilon/3. The first completion is the original
UNHALVED `Rproduct`; its actual finite formal first jet equals 2*dPartial
in the limit, at the existing named derivative cutoff. The separately proved
actual value/first/angular comparisons yield

```text
Q = 2*P(x)^2*D(x),
P(1)^2*((D(1)-D(x))*P(x)^2) = 2*w*(1-x)*A(x)^2*A(1)^2.
```

P is the ORIGINAL completed Jacobi product and D is the EXISTING completion
of the literal product radial costs. No finite P_N=F_N substitution, limit
differentiation or supplied analytic identity. Completed odd boundary pins,
not a finite normalization shortcut, supply factor four. The determinant
polynomial is checked pointwise; separately completed endpoint frequencies
supply the endpoint determinant. Only rational factor two is cancelled in
the equality.

On [-1,1] the right side is nonnegative. The actual product floor gives
P(1)^2*P(x)^2>=floor(w)^4 at EVERY approximation; existing constructive
positive-factor cancellation gives D(x)<=D(1). Its actual endpoint ceiling
therefore produces D(x)<=C_T(w)=2*w/(1-w*w) for EVERY strict 0<w<1 and rational
x in [-1,1], not just the named-nome regression cases.

The original signed finite-tail theorem then gives

```text
D_N(x) <= C_T(w) + 4*w^(2*N+1)/(1-w*w),
(1-w)*D_N(x) <= 3/2,  when w^(2*N+1)<=1/8.
```

Negative omitted terms are paid; no monotonicity of the signed costs is
asserted. `radialOnset(w)=powBaseCutoff(w,1/8)` is explicit Nat data, independent
of x. It is a sufficient onset, not a claimed sharp cutoff. These actual
costs now supply the existing finite normalized heat consumer, producing
C*h^2+(1-x*x)*(h*hxx-hx*hx)-x*h*hx>=0 at C=C_T+tail_N, with original formal
heat jets and inverse-nome/half normalization. The positive floor enters
cancellation/construction only, NEVER the upper-budget coefficient.

The ACTUAL radial class polynomial now has a constructed Type-valued Haar
certificate after adding delta>0 to C, for N>=1 at the same small-factor
onset. Its literal formal jets are pinned for all rational arguments,
including both endpoints. Positive shifted heat coefficients and the actual
heat constant prove h>=floor(w); the produced strict margin is
delta*floor(w)^2. The existing strict Bernstein compiler and unit-coordinate
certificates construct the substituted witness. The floor affects the
Bernstein row, not C_T+tail_N+delta. N=0 heat is zero, so no strict margin is
claimed there. Polynomial equalities hold under arbitrary Haar insertions;
positivity is retained only for certified positive/square insertions.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `productAngularCutoff`, `productAngularCReal`, `productAngularCReal_eq_bare` | `lean/YMGap/Continuum/ThetaProductAngularCompletion.lean:42`, `:114`, `:138` | `/private/tmp/ym-oct7-product-angular-completion1.log` |
| `productFirstCReal_formal_pin`, `frequencyNumerator_eq_productCost` | `lean/YMGap/Continuum/ThetaProductRadialCompletedPin.lean:49`, `:136` | `/private/tmp/ym-oct7-product-radial-completed1.log` |
| `cleared_addition_square` | `lean/YMGap/Continuum/ThetaCompletedAdditionSquare.lean:179` | `/private/tmp/ym-oct7-completed-addition-square2.log` |
| `productRadialCostCReal_le_cap`, `productRadialCost_nome_defect_le_three_halves` | `lean/YMGap/Continuum/ThetaProductRadialCeiling.lean:100`, `:121` | `/private/tmp/ym-oct7-product-radial-ceiling3.log` |
| `radialOnset`, `heat_radial_nonnegative_at_onset` | `lean/YMGap/Continuum/JacobiHeatRadialProducedBound.lean:32`, `:77` | `/private/tmp/ym-oct7-heat-radial-produced1.log` |
| `radialHeat_floor`, `radialPolynomial_eval`, `radialPolynomial_strict_margin`, `radialCertificate` | `lean/YMGap/Continuum/JacobiHeatRadialHaarCertificate.lean:76`, `:111`, `:153`, `:182` | `/private/tmp/ym-oct7-heat-radial-haar2.log` |

Six focused leaves/37 printed gates pass within {propext, Quot.sound}; seven
printed computational definitions are axiom-free. Root read all final source;
independent review confirms same-object normalization, cutoff dependence and
positive-floor cancellation. No source sorry/custom axiom/classical shortcut,
native_decide, canonical-field weakening or axiom-baseline refresh. Earlier
failed elaborations are not proof evidence. One local composition uses an
800000-heartbeat elaboration allowance; no memory ceiling was raised. Every
launch used a fresh dynamic process/capacity check, one 20-GiB worker and a
12-GiB reserve; preflights observed 87--88% free memory and zero swap. One
yielded check was observed again about five minutes later while independent
mathematics/source work proceeded. No concurrent compiler or broad test suite,
full-root/tree build or audit. Root imports registered, not root-built.

Final checked-source SHA256:

- `ThetaProductAngularCompletion.lean`: `ce72636a37989e217a11fa83331d0dee9edb1e2442e1552e65565a75cdef8ac0`
- `ThetaProductRadialCompletedPin.lean`: `abf56b2dff2b5a37c7411ab1d6a32778b37e581c7527b60b5e26e5faef492a16`
- `ThetaCompletedAdditionSquare.lean`: `6a76bdccb2ec94e994ff7cd4fd7fb6fea7a32465caf4b138cc4349ac3d025221`
- `ThetaProductRadialCeiling.lean`: `8f6ab2baf419cc22a187b2ea0adbe0219195ca543f8e32de949aa7c71a211acc`
- `JacobiHeatRadialProducedBound.lean`: `290078f75d0e86fee595c3d027b4c1f362b0bb2ef50b089273aff2b6916430a1`

Additional final checked-source SHA256:

- `JacobiHeatRadialHaarCertificate.lean`: `6a4ef9d652a21feda8cb2a157e48e3a48848badcf00938702243ebce43af773e`

### Next real producers and boundary

NEXT sharp intrinsic/angular curvature on the actual weighted finite heat,
then transfer to the SAME original prefix and original conditional score.
Reuse EXISTING value/first/mixed angular deficits, not a new tail engine:

- `QuaternionHaarAllNomeHeatCertificate.deficitInterval`,
  `lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:91`;
- `QuaternionHaarHeatAngularDeficit.angularDeficitInterval`,
  `lean/YMGap/Continuum/QuaternionHaarHeatAngularDeficit.lean:142`;
- `QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval`,
  `lean/YMGap/Continuum/QuaternionHaarHeatMixedAngularDeficit.lean:302`;
- the existing original-prefix transport pattern
  `QuaternionHaarHeatMixedRelativeAngularBound.heatPrefixMixedRelativeBoundAt`,
  `lean/YMGap/Continuum/QuaternionHaarHeatMixedRelativeAngularBound.lean:136`.

These existing declarations were source-inspected, not recompiled in this
checkpoint. The old relative cap is not the new sharp curvature cap. The
mixed deficit is an actual ordered ANGULAR derivative estimate, not an
ordinary scalar pderiv^2 estimate. Radial/transverse class bounds do not
automatically furnish a full intrinsic matrix or an interacting marginal.

The ceiling depends explicitly on w and is uniform only in the scalar
coordinate. The normalized bound uses 1-w, NOT an identified physical clock.
Final completed arithmetic Equiv does not expose a new combined
coordinate-uniform Type-valued modulus. The radial Haar certificate is
constructed above; no original interacting score,
all-vector OS estimate, nontrivial continuum survival, volume/spacing control,
physical mass calibration, SAME QFT, every-group construction or Clay closure
is claimed. Broad chart claims stay OPEN and unchanged; no chart reprint.

## Observed signed numerator and completed parity-series join (2026-10-07 local; checked 2026-10-08 UTC)

The previous checkpoint's literal signed-frequency numerator and actual
parity/SAME-series joins are now supplied. The user's lattice-note review
remains context, not an empirical premise:
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. The live plan continues
forward from original scalar objects and backward from the SAME physical
Hamiltonian requirements; a measured channel mass closes no analytic input.

### Actual mathematical contraction

Write L=(1-x*x)*D^2-x*D and F_N for the ORIGINAL bare theta prefix, not the
finite Jacobi Euler product. Actual squared signed frequencies give

```text
L(J_N) = -sum_(m,n) (m+n)^2*w^(m^2+n^2)*T_|m+n|(x),
M_N = sum_(m,n) (m^2+n^2)*w^(m^2+n^2)*T_|m+n|(x) = -2*F_N*L(F_N),
Q_N = 2*M_N+L(J_N) = 2*((1-x*x)*(F_N')^2-F_N*L(F_N)).
```

These pins hold for ALL rational w,x and N, including zero; no analytic
guard or positivity input. The actual Int identity
|m-n|^2+|m+n|^2=2*(|m|^2+|n|^2) is kernel-normalized, not truncated Nat
subtraction. Actual signed-list reflection and Cartesian factorization
produce M. Existing finite formal angular rules produce the first line.
Independent review confirms N=0 gives zero; N=1 gives M=4*w*x+8*w^2*x^2
and Q=4*w*x+8*w^2, which may be negative. No positivity is added.

The literal bare angular prefixes now form a constructed CReal with the
existing shell cutoff. The first-series completion is twice the existing
actual dSeriesCReal, pinned to the finite formal jet BEFORE any limit.
Arithmetic on these independently constructed series produces Q's CReal;
EVERY approximation is equivalent to the actual signed frequency-box sum.

The odd rectangle has actual unbalanced boundaries
O_N=2*H_N-h_N and O_endpoint,N=2*H_endpoint,N-h_endpoint,N. Both finite pins
hold at zero and retain their top term. Literal signed-prefix completions
use `oddSignedCutoff(w,epsilon)=oneSidedCutoff(w,epsilon/4)`, paying twice
the one-sided prefix discrepancy plus two boundary terms. The value and
independently completed frequency series each equal twice their ORIGINAL
one-sided completion. A finite factor four is never inserted.

Finally the ACTUAL completed value rectangle at y=1 equals F^2, and the
ACTUAL completed endpoint-frequency rectangle equals Q's constructed
value/first/angular numerator. The original paid rectangle lives at N+1
and the box at N; the rectangle's constructed Cauchy proof pays this offset
with half the tolerance. Endpoint scalar multiplication is commuted inside
the actual finite sums, not silently definitionally equated.

### Declaration evidence and verification boundary

| Declaration | Final source | Passing focused log |
| --- | --- | --- |
| `angular_add`, `angular_scale` (unchanged proofs exposed) | `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:87`, `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:103` | `/private/tmp/ym-oct7-angular-public-linearity1.log` |
| `joint_angular_frequency_pin` | `lean/YMGap/Continuum/ThetaJointAngularPin.lean:222` | `/private/tmp/ym-oct7-joint-angular-frequency1.log` |
| `moment_sum_factor_pin`, `moment_sum_angular_pin` | `lean/YMGap/Continuum/ThetaJointWeightedMoment.lean:92`, `lean/YMGap/Continuum/ThetaJointWeightedMoment.lean:171` | `/private/tmp/ym-oct7-joint-weighted-moment1.log` |
| `frequency_square_balance`, `frequency_box_numerator_pin` | `lean/YMGap/Continuum/ThetaJointFrequencyNumerator.lean:46`, `lean/YMGap/Continuum/ThetaJointFrequencyNumerator.lean:103` | `/private/tmp/ym-oct7-joint-frequency-numerator2.log` |
| `bareAngularCReal`, `bareAngularCReal_formal_pin` | `lean/YMGap/Continuum/ThetaBareAngularCompletion.lean:91`, `lean/YMGap/Continuum/ThetaBareAngularCompletion.lean:104` | `/private/tmp/ym-oct7-bare-angular-completion1.log` |
| `bare_first_jet_pin`, `frequencyNumeratorCReal_box_pin` | `lean/YMGap/Continuum/ThetaJointFrequencyCompletion.lean:54`, `lean/YMGap/Continuum/ThetaJointFrequencyCompletion.lean:84` | `/private/tmp/ym-oct7-frequency-completion1.log` |
| `odd_signed_boundary_pin`, `odd_signed_endpoint_boundary_pin` | `lean/YMGap/Continuum/ThetaOddBoundaryPin.lean:161`, `lean/YMGap/Continuum/ThetaOddBoundaryPin.lean:204` | `/private/tmp/ym-oct7-odd-boundary3.log` |
| `oddSignedCutoff`, `oddSignedCReal_eq_twice`, `oddSignedEndpointCReal_eq_twice` | `lean/YMGap/Continuum/ThetaOddSeriesCompletion.lean:36`, `lean/YMGap/Continuum/ThetaOddSeriesCompletion.lean:175`, `lean/YMGap/Continuum/ThetaOddSeriesCompletion.lean:190` | `/private/tmp/ym-oct7-odd-series-completion2.log` |
| `completed_value_rectangle_pin`, `completed_frequency_rectangle_pin` | `lean/YMGap/Continuum/ThetaJointRectangleCompletion.lean:97`, `lean/YMGap/Continuum/ThetaJointRectangleCompletion.lean:117` | `/private/tmp/ym-oct7-joint-rectangle-completion1.log` |

Seven new leaves and two changed leaves pass nine focused checks. All 61
printed gates in those final logs stay within {propext, Quot.sound}; fifteen
printed computational definitions are axiom-free. No source sorry, custom
axiom, classical input, native_decide, canonical field weakening or baseline
refresh. Initial failed elaborations are not proof evidence. Root read every
final source; independent review found no normalization, zero-index,
same-object or constructive-elimination defect. All runs used one 20-GiB
worker, a 12-GiB reserve and fresh dynamic capacity/process checks; observed
86--87% free memory and zero swap. No concurrent compiler/test suite, raised
limits, full-root/tree build or audit. Root imports are registered, not built.

Named angular/odd cutoffs are coordinate-uniform at each strict fixed nome,
NOT uniform in nome, coupling, spacing, physical time or volume. Final
rectangle Equiv uses the existing arithmetic CReal.cauchy thresholds solely
inside Prop. It does NOT expose a new combined, coordinate-uniform
Type-valued modulus, nor extract a modulus from Prop. No such stronger
consumer has been claimed closed.

Final checked-source SHA256; subsequent historical tables retain their
checkpoint snapshots rather than pretending to be current hashes:

- `FiniteJacobiAngularComparison.lean`: `32fcec01a53ffcf57137b8abfd8a74651d5fe67cea71f8a52dc121bb722c56c1`
- `ThetaJointAngularPin.lean`: `836cf0f500c37026d8b43fc32c3d32602b3180e9a9d6469e5eaa31645fe2422d`
- `ThetaJointWeightedMoment.lean`: `765d3800ba66a9c39e3325bd5d413ed1abb165b762f5bb60a108ba1f4fe52e06`
- `ThetaJointFrequencyNumerator.lean`: `59f4ab1f4c104cfc5ab33c74c80e486afb1cd47db06a5f0b227ebf4d3ed9413a`
- `ThetaBareAngularCompletion.lean`: `287ed43275053c976b602d86ee9b94e52a2b23cac4b61eedd54b73063e64a8e3`
- `ThetaJointFrequencyCompletion.lean`: `409fa740141a74359b6ba9d996dfaaf2184c6efb4271c3d9b5490cba8bcb1a33`
- `ThetaOddBoundaryPin.lean`: `c968a2bcaf6e955e46a9615135611c836c40cdcd744abb1e989cf0964a0a9717`
- `ThetaOddSeriesCompletion.lean`: `ed32e7b0af2de6be88fdbfa0a4b8c414a490dd7ca2d9303a7b231337a5317755`
- `ThetaJointRectangleCompletion.lean`: `4db2d7c592e2836193cc08c0fba9125277204c5027938a366aec1dbb5f54031a`

### Next actual consumer and residue

CONTINUE at the SAME Jacobi radial-cost limit, not a fresh assumed curvature
interface. The actual finite `FiniteJacobiAngularComparison.productRadialNumerator_pin`
in `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:290` identifies
the cleared product numerator with P_N^2*D_N. Join its value/first/angular
limits to the constructed numerator above using the EXISTING comparison
cutoffs and actual `JacobiProductRadialLimit.productRadialCostCReal` in
`lean/YMGap/Continuum/JacobiProductRadialLimit.lean:131`. The product's literal
angular completion/SAME-product cost pin remain required; a finite comparison
alone is not that producer. Then combine with the actual completed
alternating determinant squares to obtain the cleared addition identity
and useful whole-interval ceiling. Stop/revise on any coefficient,
normalization, original-object or cutoff mismatch. Do not replace finite
bare F_N by finite Euler P_N or differentiate a value limit.

The full addition/whole-interval ceiling, strict Haar/original conditional
join, useful signed-cost/scaling estimate, independent AF survival,
all-vector completed OS comparison, physical/volume control, SAME limiting
QFT, every compact simple group and Clay remain OPEN. The canonical broad
chart is unchanged; no reprint.

### Conflict-free remote integration

The push encountered newer R1 commits through `d5291102`. They were fetched
and merged without a force push; both additions to root imports/status were
preserved and the nine checked leaf hashes above are unchanged. Incoming
R1 declarations `theta_ceiling_half` and `theta_ceiling_ff` in
`lean/YMGap/Continuum/ThetaCeilingNamedNomes.lean:70` and
`lean/YMGap/Continuum/ThetaCeilingNamedNomes.lean:75` target this SAME
radial-cost limit, but only w=1/2 and w=4/5 with rational x in [-1,1]. The
general-nome addition route remains open. Those incoming files were inspected,
not recompiled or axiom-audited here; no broader verification is inferred
from the merge. The existing scope report remains authoritative for R1:
`audits/SCOPE-THETA-CEILING-NAMED-NOMES-2026-10-07.md`.

## Prior endpoint-jet and SAME-series checkpoint (2026-10-07; residue superseded above)

The actual completed alternating value and endpoint determinant squares
are now kernel-checked. This removes that specific series-completion input,
not the full theta/Jacobi-product addition or curvature ceiling. The
lattice-measurement note remains calibration context only, as recorded in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; no measured mass,
Sobolev regularity, area-law implication or Hamiltonian identity is assumed.

The earlier endpoint experiment below proposed a conservative factor-three
tail. The proved bound is sharper: on OMITTED cells h<=N<T=h+|k|, so both
frequencies 2*h+1 and |2*k| are <=2*T. Their squared rational difference
has absolute value <=4*T^2, not the sum of two caps. The original shell
budget and cutoff therefore pay both value and endpoint jet. The h<T guard
is load-bearing; this cap is not asserted on the whole mixed carrier.

| Declaration | Current source | Passing focused log |
| --- | --- | --- |
| `endpointCell`, `endpointCell_abs_le_cellCap` | `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:53`, `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:262` | `/private/tmp/ym-oct7-alternating-endpoint-tail2.log` |
| `endpoint_rectangle_error_le_epsilon` | `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:332` | Same mixed-tail log |
| `squareKernel_coeff_pin`, `endpointCell_sum_eq_alternating_square` | `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:157`, `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:234` | `/private/tmp/ym-oct7-alternating-endpoint-jets3.log` |
| `mixedRectanglePolynomial_endpoint_derivative`, `endpoint_rectangle_formal_jet_close` | `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:289`, `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:309` | Same endpoint-jets log |
| `endpoint_rectangle_factored_pin` | `lean/YMGap/Continuum/ThetaAlternatingEndpointRectangle.lean:109` | `/private/tmp/ym-oct7-alternating-endpoint-rectangle1.log` |
| `endpoint_determinant_square_close` | `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:322` | Same endpoint-jets log |
| `bareTheta_signed_pin`, `theta_box_endpoint_value_pin` | `lean/YMGap/Continuum/ThetaJointValuePin.lean:152`, `lean/YMGap/Continuum/ThetaJointValuePin.lean:283` | `/private/tmp/ym-oct7-theta-joint-value5.log` |
| `joint_coeff_pin`, `joint_angular_pin` | `lean/YMGap/Continuum/ThetaJointAngularPin.lean:101`, `lean/YMGap/Continuum/ThetaJointAngularPin.lean:160` | `/private/tmp/ym-oct7-theta-joint-angular2.log` |
| `oneSidedCutoff`, `shellPrefix_cauchy` | `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:41`, `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:173` | `/private/tmp/ym-oct7-theta-onesided-completion3.log` |
| `alternatingCReal`, `oddCReal`, `oddEndpointCReal` | `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:256`, `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:261`, `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:266` | Same one-sided log |
| `evenCReal`, `evenEndpointCReal` | `lean/YMGap/Continuum/ThetaEvenSeriesCompletion.lean:172`, `lean/YMGap/Continuum/ThetaEvenSeriesCompletion.lean:179` | `/private/tmp/ym-oct7-theta-even-completion2.log` |
| `completed_alternating_square_pin`, `completed_endpoint_square_pin` | `lean/YMGap/Continuum/ThetaAlternatingCompletedPin.lean:51`, `lean/YMGap/Continuum/ThetaAlternatingCompletedPin.lean:69` | `/private/tmp/ym-oct7-alternating-completed-pin1.log` |

The finite half-diamond value identity is reflected into actual coefficients
BEFORE formal endpoint differentiation. The endpoint rectangle is its actual
polynomial, not a substituted square. At N=1 its excess remains 10*w^6.
The literal E/H endpoint determinant is factored independently, with H
one-sided. All five CReal constructors retain their exact original N-th
prefixes. Their differences start at index min(m,n)+1: index zero is not
incorrectly bounded by the vanishing zero shell. A named Nat cutoff fills
the legacy CReal.cauchy field; no modulus witness is extracted from Prop.
Uniformity is in x on [-1,1] at named 0<w<1, NOT in nome or physical scale.

The SAME finite paid estimates now give

```text
K(x)=E(1)*H(x)-H(1)*E(x)=(x-1)*A(x)^2,
E(1)*H_endpoint-H(1)*E_endpoint=A(1)^2.
```

The second is a separately completed frequency identity; it does not claim
a derivative of a value limit. The original joint box at y=1 is pinned to
bare F_N^2, including its central one and factor two. Coefficient reflection
then gives its actual angular product-rule jet. Finite Euler P_N is never
substituted for F_N. The full signed-frequency numerator is NOT proved yet.

### Exact verification boundary

Seven new leaves and the changed mixed-tail leaf pass their focused checks.
All 68 printed gates in the eight final logs above stay within
{propext, Quot.sound}; fourteen printed computational definitions are
axiom-free. The other constructed CReal definitions carry their actual
Cauchy proofs, with permitted axiom dependencies. No new source sorry,
axiom, classical input, native_decide, field weakening or baseline refresh.
Root inspected the complete final sources; independent mathematical review
confirmed index-zero handling, normalization, signed cancellation, named
cutoffs and separate endpoint completion. Initial elaboration failures
(imports/names, parentheses, scalar congruence and implicit Nat numerals)
and the repaired omega classical leak are not proof evidence.

Final checked-source SHA256 (earlier tables retain their historical hashes):

- `ThetaAlternatingMixedTail.lean`: `167c39fe3328b3a546c387993334e5e6fd2f12457e24d0290c360cc095a01947`
- `ThetaAlternatingEndpointJets.lean`: `d1d63242df05424771bfe88cb931391f6d64b8869d685b7947fa7cd6fcfd3f66`
- `ThetaAlternatingEndpointRectangle.lean`: `0659811e74cb990482635bd8d93a93cccc285692dba9c0f1894d26dd58f106c3`
- `ThetaJointValuePin.lean`: `aac8a79b93a9056f798481faef97bd6735a858cc5d4ef991d04fd91b05065428`
- `ThetaJointAngularPin.lean`: `a9eec00d82135fd1b95011cb64f301ef584bcbec53bd238cb6780ff7930cccde`
- `ThetaOneSidedSeriesCompletion.lean`: `db7297ae26b4acaa34b9d5559e786edff7d1fbe56f8cd62115c3db760731a400`
- `ThetaEvenSeriesCompletion.lean`: `dfa3a102495553d0b87f51c65a83adcbc952643cb6a62cfa2761b3422601a02f`
- `ThetaAlternatingCompletedPin.lean`: `154da9ecf23d17281b241b7893916dbc09497033ce7c39b8d541bcc06c39944a`

All checks used the monitored launcher, one 20-GiB worker, 12-GiB reserve,
fresh capacity/process checks, 87--88% free memory and zero swap. No limits
raised, concurrent compiler, full-root/tree audit or broad test suite.
Root imports are registered without claiming a root build. The canonical
broad chart claims are unchanged; no chart reprint.

### Prior bounded experiment (now supplied above)

CONTINUE on the literal finite bare-theta frequency numerator. With
L=(1-x*x)*D^2-x*D, J_N=F_N^2 and
M_N=sum_(m,n) (m^2+n^2)*w^(m^2+n^2)*T_|m+n|(x), prove the actual pins

```text
L(J_N)=-sum_(m,n) (m+n)^2*w^(m^2+n^2)*T_|m+n|(x),
M_N=-2*F_N*L(F_N),
Q_N=2*M_N+L(J_N)=2*((1-x*x)*(F_N')^2-F_N*L(F_N)).
```

The first uses actual finite angular ODE and sum transport; the second uses
signed reflection/product-to-sum and actual Cartesian factorization. The
coefficient-pinned angular square rule is now supplied. No analytic premise
is needed for these finite steps. Prediction/test: N=0 gives zero; N=1
gives Q_N=4*w*x+8*w^2, which can be negative. Do NOT add positivity or an
Euler-product finite identity. Reuse existing exact signed-list permutations
and explicit original coefficients; revise if a coefficient or SAME-object
pin fails. Verification stays narrow, serialized and capped.

Then compose actual parity rectangle limits, explicitly pay the unbalanced
odd boundary, and join to the literal Jacobi-product value/first/angular
limits using the existing comparison cutoffs. The full addition-square
curvature ceiling, strict Haar/original conditional join, useful signed
cost/scaling estimate, independent survival, completed OS comparison,
physical/volume control, SAME limiting QFT, every group and Clay remain OPEN.

## Selected actual parity-tail join

The next finite target is the absolute discrepancy between each actual
even/odd diamond sum at cutoff N and its literal ambient rectangle
`boxIndices (N+1)`, for BOTH theta values and endpoint-frequency-square
weights. Use the exact filter partition, not a same-cutoff rectangle
identity. Omitted cells have radius T>N, and inside the ambient rectangle
T<=2*N+3. Explicit four-sector lists of length 4*T must cover every such
shell. Their actual frequency-weighted cells pay at most
`4*T^2*w^(T^2)`; unweighted cells pay less at T>=1. Thus each omitted sum
must be bounded by `finSum (fun j => 16*(N+1+j)^3*w^((N+1+j)^2)) (N+3)`.
The existing scalar tail cutoff at epsilon/2 then pays both branches.

Inputs are literal parity exponent/frequency pins and actual Chebyshev
bounds, not supplied shell-count or discrepancy estimates. Decisive cases:
N=0, T=1, both negative indices, and shifted odd endpoints. A symmetric
integer odd rectangle is NOT paired under j -> -j-1; its boundary term
must remain until a justified later join. This step does not assert the
completed addition square, a radial curvature ceiling, or an operator gap.
Verification remains root-only serialized focused safe-launcher checks,
one 20-GiB worker and 12-GiB reserve with fresh capacity checks; no limit
raises, full-tree audit, or new assumed analytic interface.

### Observed actual weighted-tail contraction

This earlier checkpoint is commit `9d094a29`; its source lines and hashes
below identify that pre-generalization version. The reused shell engine's
current source and verification are recorded in the later alternating join.

Three new serialized focused checks PASS, with 24 printed public gates
within {propext, Quot.sound}; the two budget/cutoff definitions are
axiom-free. The existing convolution leaf also passes after making its
unchanged NoDup proof public. No sorry/axiom/classical premise, limit raise,
baseline refresh or full-root/tree audit.

| Declaration | Source | Passing log |
| --- | --- | --- |
| `evenShellIndices_length`, `oddShellIndices_length` | `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:54`, `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:60` | `/private/tmp/ym-oct7-parity-shell-enumeration3.log` |
| `evenShellIndices_mem_of_radius`, `oddShellIndices_mem_of_radius` | `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:66`, `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:161` | Same enumeration log |
| `evenFrequencyCell_abs_le`, `oddFrequencyCell_abs_le` | `lean/YMGap/Continuum/ThetaParityShellWeights.lean:152`, `lean/YMGap/Continuum/ThetaParityShellWeights.lean:170` | `/private/tmp/ym-oct7-parity-shell-weights2.log` |
| `theta_rectangle_factored_pin`, `frequency_rectangle_factored_pin` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:394`, `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:406` | `/private/tmp/ym-oct7-parity-diamond-tail6.log` |
| `theta_box_factored_error_close`, `frequency_box_factored_error_close` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:424`, `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:442` | Same diamond-tail log |
| `rectangleTailCutoff` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:308` | Same diamond-tail log; axiom-free |
| `boxIndices_nodup` (unchanged proof, now public) | `lean/YMGap/Continuum/ThetaParityConvolution.lean:171` | `/private/tmp/ym-oct7-parity-convolution-public-nodup.log` |

Final checked-source SHA256:

- `ThetaParityShellEnumeration.lean`: `7de2b98044f1906c17369670e409a658e594e5b26609c8518c7ecefa5cb72c09`
- `ThetaParityShellWeights.lean`: `eb0201f8c80cbd8a745634d3cc5828ceb5948bc56b4fbb1f299f461037293005`
- `ThetaParityDiamondTail.lean`: `a064b42190f559b16c76d959927e3135e34ae5cd09d9369539f6540249ad79e6`
- `ThetaParityConvolution.lean`: `36af6727e975686e41a9a094ebc9e28c72821778e20b924726e231c8017d6a47`

The first enumeration attempt mishandled j=0,k=-T and casted Nat
subtraction; the final proof isolates that vertex on side 3. The final
kernel check covers N=0, T=1 and all signed indices without numerical
sampling. Independent review checked the actual range, finite injection,
factor 16, signed error and odd normalization. All launches used one
20-GiB worker, 12-GiB reserve and fresh live capacity checks (87--88% free,
zero swap). Only focused targets were checked; registering root imports is
not a root-build claim. Completed addition/whole-interval ceiling,
Haar/conditional/scaling and all Clay-facing requirements remain OPEN.

### Next selected finite target (RESEARCH, not a Lean premise)

For C_n=`ChebyshevHalfShiftProduct.halfShiftCoord n x`, consider
`A_N=sum_(n=0..N) (-1)^n*w^(n*(n+1))*C_n`,
`H_N(x)=sum_(h=0..N) w^(2*h*(h+1))*T_(2*h+1)(x)` and
`E_N(x)=sum_(k=-N..N) w^(2*k^2)*T_|2*k|(x)`.
The candidate exact finite square is

    (x-1)*A_N^2
      = sum_(h>=0,k in Int,h+|k|<=N)
          w^(2*h*(h+1)+2*k^2)*(T_(2*h+1)(x)-T_|2*k|(x)).

`halfShift_product` supplies the pairwise kernel. The selected constructive
bijective reindex uses the existing parity decoder on (n,m): the even
sector maps to (h,k) with |k|<=h; the odd sector maps to |k|>=h+1 and its
alternating sign reverses the Chebyshev difference. At this selection point
the exact bijection, alternating-sign/exponent pins and mixed omitted-sum
proof were OPEN, not supplied assumptions; they are now proved in the
observed section below. The intended rectangular difference is
`E_N(1)*H_N(x)-H_N(1)*E_N(x)`; its omitted cells have N<h+|k|<=2*N
and should be paid by the existing actual even shells. Decisive tests are
N=0 and N=1 (candidate omitted payment at N=1 is
`2*w^6*(T_3(x)-T_2(x))`), signed k and both sign sectors.

H_N is one-sided: it is HALF the balanced bilateral odd sum. Using a full
bilateral odd sum instead changes the square's coefficient to
`2*(x-1)*A_N^2`. The unbalanced rectangles in the checked theorem above
must retain their boundary term. Do not claim finite factor four or a
completed square before the corresponding tails and SAME limit joins.
Keep the next implementation to this finite producer and its shell
consumer; no new assumed positivity or frontier bundle is needed.

Selected implementation split: Sol constructs the literal Cartesian
alternating-square expansion and the explicit mixed half-diamond bijection;
root proves the actual exponent/frequency/sign transport and composes them.
The mixed omitted-cell tail can reuse the already-proved finite shell
injection by generalizing its decidable carrier, not by copying a new tail
engine or adding an assumed analytic estimate. A second bounded Sol task
will instantiate it on the actual mixed rectangle. Independent review
checks the finite map, N=0/1, signed k and the one-sided odd normalization.
The predicted finite square and its epsilon error are mathematical
propositions to prove, not supplied fields. Stop/revise if a parity sign,
truncated subtraction, cutoff domain or SAME nome/coordinate fails to match.
Verification stays root-only, serialized focused checks, one 20-GiB worker,
12-GiB reserve and fresh dynamic-capacity checks, with no full-tree audit
or limit raise. Completed series/jet composition and the actual radial
ceiling remain the downstream consumers and are still OPEN.

### Earlier actual alternating-square contraction (2026-10-07 23:26 UTC)

This is checkpoint `e02ff556`; its mixed-tail lines and hash refer to that
pre-endpoint version. Current endpoint sources and evidence appear above.

The selected finite producer and actual shell consumer PASS. The checked
square is exactly `(x-1)*A_N(x)^2` on the mixed half-diamond. The actual
rectangle factors as `E_N(1)*H_N(x)-H_N(1)*E_N(x)`, with ONE-SIDED H and
the original bilateral E; its difference from the square is paid by the
existing `shellTailCutoff(w,epsilon)`. No analytic discrepancy, sign,
reindexing, factorization or counting premise is supplied. The identity
covers all rational w,x,N; the error requires named 0<w<1 and -1<=x<=1.
Uniformity is in x, NOT in nome, volume, physical time or spacing.

| Declaration | Current source | Passing log |
| --- | --- | --- |
| `alternatingPartial_square_expansion` | `lean/YMGap/Continuum/ThetaAlternatingKernel.lean:99` | `/private/tmp/ym-oct7-alternating-kernel1.log` |
| `positiveSquare_halfDiamond_permutation`, `listQSum_positiveSquare_halfDiamond` | `lean/YMGap/Continuum/ThetaAlternatingHalfDiamond.lean:485`, `lean/YMGap/Continuum/ThetaAlternatingHalfDiamond.lean:520` | `/private/tmp/ym-oct7-alternating-half-diamond4.log` |
| `cellCap`, `finite_shell_sum_bound` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:40`, `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:117` | `/private/tmp/ym-oct7-parity-generic-shell.log` |
| `mixed_rectangle_error_le`, `mixed_rectangle_error_le_epsilon` | `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:172`, `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:203` | `/private/tmp/ym-oct7-alternating-mixed-tail1.log` |
| `mixed_rectangle_factored_pin` | `lean/YMGap/Continuum/ThetaAlternatingMixedRectangle.lean:104` | `/private/tmp/ym-oct7-alternating-mixed-rectangle2.log` |
| `alternatingPairCell_encodeMixed_pin`, `alternatingPartial_halfDiamond_square` | `lean/YMGap/Continuum/ThetaAlternatingMixedPin.lean:141`, `lean/YMGap/Continuum/ThetaAlternatingMixedPin.lean:174` | `/private/tmp/ym-oct7-alternating-mixed-pin1.log` |
| `alternatingPartial_factored_error_le_epsilon` | `lean/YMGap/Continuum/ThetaAlternatingMixedPin.lean:222` | Same mixed-pin log |

Final checked-source SHA256:

- `ThetaAlternatingKernel.lean`: `57146f90eea4784b0accfc8a7253561cfddb1b52e09fd494e0c0ad4dcf057257`
- `ThetaAlternatingHalfDiamond.lean`: `ce23c437090d09b02a3737ef36fdadcfd981f3b6df4f926812b901121d413fa8`
- `ThetaAlternatingMixedTail.lean`: `77dbf3f062d46e73db9ed26647aa0871a9bfbb88e0835e1f46dde31fb9e9dbb3`
- `ThetaAlternatingMixedRectangle.lean`: `97e6b16dca39607ca42d684888af515f8c8d5218db745515231fa26c623a9ab4`
- `ThetaAlternatingMixedPin.lean`: `6c18aab0241b9d6d9ba82964cc86f7f2894c7fd351b0f45da219e6a57f167a78`
- `ThetaParityDiamondTail.lean` (current generalized engine): `7a71cbc8b95736b08ff4caf44c19b1070c04bd7ca3d70a04ecd2928c9efaf536`

The five new focused leaves pass 42 printed public gates within
{propext, Quot.sound}; ten definitions are axiom-free. The existing shell
leaf passes every old gate plus its two newly public gates. Root inspected
all sources and independently checked the even/odd algebra. Read-only
mathematical review found no sign/normalization defect. N=0 gives T1-T0.
At N=1 the half-diamond is
`T1-T0 + 2*w^2*(T1-T2) + w^4*(T3-T0)`; the rectangle adds exactly
`2*w^6*(T3-T2)`. Universal checked statements cover these cases without
sampling. Both signed k branches and the odd-sector reversal are retained.

Initial cast/projection elaboration failures and an omega-on-pair/conjunction
Classical.choice leak were repaired; only the final sources/logs above are
proof evidence. The temporary isolated pair-algebra check is diagnostic,
not an additional repository proof. No new source sorry/axiom/classical
premise, canonical field change, baseline refresh or full-root/tree audit.
All launches were serialized through the safe launcher: one 20-GiB worker,
12-GiB reserve, fresh 88%-free zero-swap capacity checks, no competing
compiler and no limit raises. Root imports registered, not root-built.
Completed addition/whole-interval radial ceiling, strict Haar/original
conditional/scaling and every Clay-facing requirement remain OPEN.
The canonical broad chart state is unchanged; no reprint.

### Next selected join: endpoint jets and SAME limits (RESEARCH)

Do not differentiate the completed value identity without a derivative
producer. The required finite endpoint cell is

    w^(2*h*(h+1)+2*k^2) * ((2*h+1)^2-(2*k)^2).

Its HALF-DIAMOND sum should equal A_N(1)^2 by reflecting the proved finite
square into actual coefficient polynomials before formal differentiation.
The RECTANGLE endpoint derivative is not equal to that square at finite N:
the N=1 excess is `10*w^6`. It needs its own omitted-jet payment. For
positive radius T=h+|k|, the proposed absolute frequency difference is
at most 9*T^2; existing 4*T shell coverage then suggests a conservative
`3*omittedBudget`, and a cutoff at epsilon/3. These are propositions to
prove, NOT new inputs or assumed derivative limits.

Available inputs: `ChebyshevFormalJets.coefficients_of_eval_eqv`,
`CoeffEqv.pderiv`, `pderiv_pmul`, `pderiv_padd`, `pderiv_pscale`,
`QPoly.eval_pmul`, `eval_padd`, `eval_pscale`, and the literal mixed-tail
engine above. Build only the necessary half-shift/alternating coefficient
polynomials, not a new calculus. Downstream SAME-object residues include
the actual joint value J_N(x,1)=bareTheta_N(x)^2, the endpoint-frequency
numerator pin to its actual first/angular jets, and the product-limit join
using `Ppart_sub_bareTheta_close`, `fullProdDx_sub_two_dPartial_close`,
`productAngularJet_sub_bare_close` and `productRadialNumerator_pin`.
Keep actual prefix approximants and the existing `KPLimit.crealOfTail`
construction/moduli when composing CReal limits. Retain the unbalanced
odd boundary through this join; do not silently insert a finite factor four.

Continue this finite producer/jet route, with N=0/1 as decisive tests.
Stop/revise if finite rectangle and half-diamond jets are conflated, a
derivative is inferred merely from value convergence, or the bare theta
prefix is substituted for the finite Euler product. Verification remains
serialized focused checks under the unchanged dynamic-memory contract.
The intended addition-square curvature ceiling is still an analytic
producer to establish, not an inhabited premise.

## Mathematical selection before implementation

The previous checkpoint proves an unweighted whole-product norm-loss law
and refutes arbitrary positive output weighting. Do not reopen that shortcut.
The exact original terminal variance balance already exists, so no new
stationarity wrapper is needed.

The remaining joint-score step needs direction coefficients that depend on
the output, not just a fixed rational vector. For the six rotations at ONE
block, set Mij=h*Di(Dj h)-(Di h)*(Dj h), U=C(w)*h^2. The existing ORIGINAL
heat certificates give both U+Mij and U-Mij. The missing finite construction
is a certificate for

    6*U*sum_i ui^2 + sum_ij ui*uj*Mij,

for supported POLYNOMIAL ui. Every ordered mixed entry is retained. The
square identity

    U*(v^2+z^2)+2*M*v*z
      = ((U+M)*(v+z)^2+(U-M)*(v-z)^2)/2

constructs each pair; half-summing all ordered pairs gives the desired
six-column envelope. No coefficient is differentiated. This is the FROZEN
Hessian, not D_u(D_u h), which would add derivative-of-ui terms.

Inputs: `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:152`,
`heatLogHessianBounds`, and the supported square/product/transport
constructors in `QuaternionHaarSquareCertificate.lean`. Existing
`SU2QuaternionProductHeatSignedLogCurvature.productHeat_signedCurvature`
uses rational constant coefficients and is not this substitution theorem.

Downstream consumer: the missing adaptive whole-product/conditional Gram
estimate for S_i=A*Di b-b*Di A. **No declaration currently implements that
complete adaptive join.** The local certificate is one needed input, not
the joint-score theorem itself. The complete original V source, paired
residual, output weight and terminal mismatch must survive the eventual
join. Do not use the equal-endpoint integrated Hessian sign on a conditional
law, and do not turn a qMax/A upper comparison into a useful spatially
uniform constant by omitting its denominator dependence.

Decisive tests: zero coefficients, signed/cross coefficients, and coefficients
depending on the differentiated output coordinate. The frozen definition
must remain valid without derivative-of-coefficient terms. m=6 is the local
number of rotations, NOT an active-block or volume count. C(w) retains its
genuine nome dependence; it is not AF-uniform.

Verification budget: root alone runs serialized narrow safe-launcher checks,
one 20-GiB worker, 12-GiB OS reserve, fresh live capacity preflights. Sol owns
only the finite envelope; root owns the actual-heat instance. Stop/revise if
the proof assumes a Hessian sign, discards action factors, imports another
carrier, requires limit raises or expands into unneeded generic scaffolding.

## Observed evidence

Three serialized focused checks PASS, with four printed declarations
depending only on {propext, Quot.sound}:

| Declaration | Source | Passing log |
| --- | --- | --- |
| `two_polynomial_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:74` | `/private/tmp/ym-oct7-six-polynomial-matrix3.log` |
| `six_polynomial_matrix_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:134` | Same matrix log |
| `heat_frozen_six_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionFrozenSixHeatCurvature.lean:58` | `/private/tmp/ym-oct7-frozen-six-heat2.log` |
| `lastStep_frozen_six_score_curvature_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreCurvature.lean:64` | `/private/tmp/ym-oct7-frozen-six-original-score.log` |

Log SHA256, in the three-log order above:

```text
7bd0e0e6892d80a6068934434af5d4f10a77abdb330f092cdb9b70a47c931a9c
f47dfd9f2d640368cdea9eb97e14c5bbc48ca17d955dbc23eab0c4a75a1c9604
67a5f852735f6f92699c2ede3aef0c887f7f68f83f75db66ff48193daed5b1a4
```

Earlier elaboration failures were a pre-import module-comment form, a missing
parenthesis and defining namespace opens; they are not proof evidence.
No limits were raised. Root and Sol inspected the finite producer; independent
read-only review found no mathematical defect in its ordered-pair identity
or the actual factor/score instance. No new sorry, axiom, classical input,
canonical field change or scorecard closure. Root import registration only;
no full-root/tree audit or hashed-baseline refresh.

Observed capacity before the last two launches: 87--88% memory free, zero swap,
no competing compiler. Every check used one 20-GiB worker and 12-GiB reserve.
The universal polynomial-coefficient type includes zero, signed and
output-coordinate-dependent coefficients; the resulting expression is
explicitly frozen, with no differentiated coefficients. No separate numerical
test or original conditional-score inequality is claimed.

## Interpretation and next decision

CONTINUE at the whole-product frozen-Hessian/conditional Gram join. The local
adaptive restriction is removed; a global estimate is NOT supplied. Preserve
cross-block terms, the original interacting source/action and output weight,
actual normalization and terminal mismatch. Do not sum copies of a global
loss at every block or infer a conditional integrated Hessian sign.

The next finite algebraic target uses frozen jets d_p=sum(u_i*Di p),
e_p=sum(u_i*u_j*Di(Dj p)), with polynomial costs R_p,R_q:

```text
d_pq = d_p*q+p*d_q
e_pq = e_p*q+2*d_p*d_q+p*e_q
(R_p+R_q)*(p*q)^2+(p*q)*e_pq-d_pq^2
  = q^2*(R_p*p^2+p*e_p-d_p^2)+p^2*(R_q*q^2+q*e_q-d_q^2).
```

This is the proposed tensorization identity, NOT a newly checked declaration.
`lean/YMGap/Continuum/QuaternionHaarProductLogCurvature.lean:30`,
`productLogCurvatureLower`, has the scalar-cost version; the required
polynomial-cost and actual frozen-derivative pins remain missing.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:118`,
`kineticWeight_eq_indexedProduct`, is the SAME-kernel consumer pin.
Local costs should add as 6*C(w)*sum_s sum_i u_(s,i)^2; product cross terms
cancel in the log-Hessian numerator, not by claiming cross derivatives vanish.

The user's lattice-measurement note is already incorporated in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and the live plan.
It changes no proof premise: fitted-channel masses are not every-state gaps,
and an exact discrete transfer logarithm does not bypass physical-clock or
limiting-theory identification. The SAME completed comparison, justified
scaling family, nontrivial survival and limiting QFT remain open. This local
certificate closes no broad chart node or Clay obligation.

## Next experiment: polynomial-cost tensorization

Selected target: construct the displayed product-jet identity, then instantiate
it with local frozen heat jets on the literal original product. The adaptive
coefficient restriction is already removed. The missing input here is additive
polynomial-cost assembly, not another scalar smoothing estimate.

Available inputs are the local six envelope, supported opposite-square
multiplication and the existing scalar product identity. Predicted result:
local costs add, cross products cancel exactly and no active-count multiplier
appears. Decisive tests: empty product, duplicate factors, arbitrary signed
and output-dependent coefficients. Differentiate only the heat factors, never
the coefficients. A recursive formal jet is not yet a direct differential
or conditional integral pin; keep that boundary explicit.

Verification budget remains serialized focused checks with one 20-GiB worker,
12-GiB reserve and fresh dynamic process/memory preflights. Root verifies;
Sol supplies only the finite product identity; an independent reviewer inspects
the actual join. Stop/revise if an integrated log-Hessian sign is assumed,
cross-block derivatives are dropped, source/action/output weights change or
the proposed consumer needs a missing derivative pin.

### Observed tensorization evidence

Three serialized focused checks PASS; six printed declarations use only
{propext, Quot.sound}:

| Declaration | Source | Passing log |
| --- | --- | --- |
| `polynomialJet_product_curvature_certificate` | `lean/YMGap/Continuum/QuaternionHaarPolynomialJetCurvature.lean:49` | `/private/tmp/ym-oct7-polynomial-jet-curvature.log` |
| `frozenSixHeatEnvelope_jet_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:95` | `/private/tmp/ym-oct7-product-frozen-jets3.log` |
| `heat_frozen_six_jet_certificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:109` | Same product log |
| `productHeat_frozenJet_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:153` | Same product log |
| `lastStepScoreCoefficients_supported` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lean:53` | `/private/tmp/ym-oct7-original-frozen-score-product.log` |
| `original_kinetic_frozenScoreJet_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lean:70` | Same original-score log |

Log SHA256 in the three-log order above:

```text
f9f1ae8b3fc81457d7eef94ad58958ea6932ac3648746edfc0cbbd155afd78be
7a7368679cfa73d66192262f51560fdd47fe9654aa3f743717638a693f1f4e40
079c9ac6e4340329594c57e1bdd727dfdfa99b523fc56af411bac47d662c8730
```

The first product attempt failed on a defining namespace; the second failed
because a constant-zero polynomial is not definitionally the empty zero list.
The repaired empty-product transport uses `RatPolyCoeffEqv.zero_smul`, not a
limit raise or changed claim. Those failed logs are not proof evidence.
Each launch had a fresh capacity/process preflight: 87--88% free, zero swap,
no competing compiler. No new source sorry/axiom/classical input or canonical
field change; root import registration only, no full-root/tree audit or
hashed-baseline refresh. Empty and duplicate-factor cases are in the universal
recursive theorem, not separate numerical claims.

### Interpretation and remaining exact joins

CONTINUE. The local matrix-to-heat-jet pin and additive polynomial-cost product
construction are checked, including the original kinetic base and actual
transfer-score coefficients. They do NOT yet assert that the recursive jets
equal a direct whole-kernel frozen angular sum. The missing differential pins
are precisely the first/second frozen Leibniz rules and factor localization;
coefficients must not be differentiated.

The subsequent conditional target retains the Hessian:
S_u^2 <= Noise*(R*A^2+A*F2(A)-F1(A)^2), with A=T a, and only under the
genuine positive conditional law and a justified source factorization/error
join. For arbitrary original c, do not silently set phi=c/a. The existing
incoming reciprocal/error construction remains required where appropriate.
Output coefficients must pull through head integration before this target is
an actual original-score statement. `partialHaarHeads_mul_lift` in
`lean/YMGap/Continuum/SU2QuaternionHeadChainComposition.lean:51` and
`angularDerivative_partialHaarHeads` in
`lean/YMGap/Continuum/SU2QuaternionHaarTailDerivative.lean:171` are the existing
pin inputs. Polynomial-column Gram alone does not supply the score column
F1(K)/K; a cleared square/order-reflection join is still missing.

Do NOT assume an integrated log-Hessian vanishes: free marginal cancellation
is only integral DD K=0. With full unweighted Haar and a constant angular
generator, H[h*D^2h-(Dh)^2]=-2*H[(Dh)^2]; conditional/action/output insertions
retain their own derivatives. No such sign or cancellation is imported here.

The nome cap still includes `heatSecondDerivativeCap/headFloor+relativeCap^2`
(`lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:143`,
`secondRelativeCap`, and `:148`, `logCurvatureCap`). No useful near-one-nome
or physical scaling control is supplied by additive tensorization.
The broad chart and Clay status remain OPEN and unchanged.

## Decisive parameter screen selected before further derivative scaffolding

Independent source review identified a cap issue: the current entrywise bound
uses the reciprocal global heat floor. Before investing in more differential
joins, test the conservative cleared proposition

    4224 <= (1-w)^2 * logCurvatureCap(w).

Available inputs: the EXISTING `headFloor_le_nome_defect_square`,
`lean/YMGap/Continuum/BF4ExactSlabHeadFloorNomeCeiling.lean:61`; the zeroth-term
`prefix_bound`, `lean/YMGap/Continuum/SU2HeatPolynomialPrefixBound.lean:105`;
and the literal cap formulas. This screen concerns the chosen bound only,
NOT the true optimal curvature, any noise, retained signed Hessian or YM gap.

Predicted outcome: the screen passes; additive product algebra cannot make
this cap bounded or inverse-linear in the nome defect. If confirmed, prioritize
a sharper ONE-SIDED lower-curvature producer or the complete signed-cost route
over further wrappers around this entrywise cap. Cancellation/noise estimates
are not refuted and must not be dropped. The screen is a rational theorem
with the same gate/single-worker budget, not a numerical parameter sweep.
Observed evidence: focused check PASS, three declarations within
{propext, Quot.sound}:

- `prefixBudget_one_le`,
  `lean/YMGap/Continuum/SU2QuaternionLogCurvatureCapObstruction.lean:37`;
- `heatSecondDerivativeCap_ge_4224`, same source `:46`;
- `logCurvatureCap_nome_defect_square_lower`, same source `:59`.

Accepted log `/private/tmp/ym-oct7-log-curvature-cap-obstruction2.log`, SHA256
`71baf4d2702ff7f2426971442fecaa270a8d1985f7964acff9a7e508bdf80c95`.
An earlier failed check omitted the explicit reciprocal positivity proof;
the repair supplies the existing `headFloor_positive`, with no limit raise
or changed statement. No new source sorry/axiom/classical input or canonical
field change. The same fresh preflight/single-worker limits apply; no full
audit or root rebuild.

Decision: REVISE the analytic priority toward the one-sided producer or
complete retained signed-cost estimate. Bounded direct derivative pins remain
useful algebra, but do not treat this entrywise cap alone as a scaling
producer. Do not infer a theorem about noise or surviving variance from
a theorem about the cap. Independent review confirms this distinction and
the accurate recursive-versus-direct jet boundary.

### One-sided research benchmark, not a formal input

Hamilton's original *A Matrix Harnack Estimate for the Heat Equation*,
Corollary 4.4 (pp. 125--126), bounds the covariant log Hessian of a positive
heat-equation solution below by -g/(2*t) on compact manifolds with nonnegative
sectional curvature and parallel Ricci tensor; it explicitly includes spheres.
This is a possible one-sided benchmark, not a Lean theorem or finite-prefix
certificate. Root checked the original-paper transcription; direct publisher
PDF requests returned 403.
[Original paper transcription, Corollary 4.4](https://doczz.net/doc/7681685/a-matrix-harnack-estimate-for-the-heat-equation),
[publisher record](https://doi.org/10.4310/CAG.1993.v1.n1.a6).

Our inference for a possible route: prove the constructive kernel/heat-time
identification and one-sided lower-curvature estimate, then transfer it to
the original finite prefix using an explicit value/derivative deficit and
positivity margin. None of these joins is supplied by citing the paper.

There is a frame distinction: for a frozen ambient rotation field X(x)=B*x
on the unit sphere, its tangent acceleration is B^2*x+|B*x|^2*x. Consequently
D_X^2(log h) includes the covariant Hessian AND the log-gradient paired with
this acceleration. That term must be controlled or removed by a justified
frame change, not silently omitted. Constant left-invariant SU(2) directions
are a candidate geodesic frame in a bi-invariant metric, but their exact
comparison with the existing six-rotation jets is unproved here.

Do not confuse this desired LOWER bound with the stronger Ricci-two UPPER
curvature expression already refuted at the original antipode; see
`audits/AUDIT-ORIGINAL-ANTIPODAL-CURVATURE-2026-10-03.md`. Do not claim
any curvature method succeeds or fails from this benchmark. The actual
conditional Hessian, original source/action, output weight, normalization,
nontrivial survival and all-vector limiting-theory joins remain required.

## Next selected experiment: exact paired-score frame join

Target: write the SAME coupled-score energy in three paired directions,
without changing its action, source, terminal messages or output multiplier.
For Sij=A*Dij(b)-b*Dij(A), the first-jet pin Sij=xi*Fj-xj*Fi,
Fj=A*partial_j(b)-b*partial_j(A), implies the coefficient-exact identity
S01*S23-S02*S13+S03*S12=0. Consequently

    (S01+S23)^2+(S02-S13)^2+(S03+S12)^2 = sum_(i<j) Sij^2.

The opposite-sign triple has the same energy. Available inputs are literal
angular differentiation, `conditionalScore` and polynomial ring reflection.
The actual consumer is `exactScoreAngularBudget`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean:112`:
retain its A=g_(n+r+1), b=T^(r+1)(g_n*psi), Vbar^2*G^2, sigma and active list.
Predicted outcome: exact equality for arbitrary supported or unsupported
polynomial A,b and arbitrary multiplier, including zero scores; no inverse,
conditional-law restriction or stationary measure is needed. This removes
the energy-conversion obstruction to trying a three-direction producer, NOT
the missing producer, geometric frame identification or conditional join.

Verification budget: two narrow serialized checks, fresh dynamic preflights,
one 20-GiB worker and 12-GiB OS reserve. Sol implements finite algebra only;
root checks it and the original consumer. Revise if a sphere/unit-radius
hypothesis is needed for the coefficient identity, weights change, or an
unproved geodesicity/heat-time/Harnack claim is used as a premise.

### Independent Jacobi test (research calculation, not kernel evidence)

The SAME positive Jacobi derivative has a better hemisphere-local estimate:
with r_k=2*w^(2k+1)/(1+2*w^(2k+1)*x+w^(4k+2)), its positive-mixture
log Hessian retains E(r_k^2)+Var(r_k). For x>=0, sum r_k and sum r_k^2
are bounded respectively by 2*w/(1-w^2) and 4*w^2/(1-w^4), with no global
Euler-floor reciprocal. Original K(V*source) is not hemisphere-supported;
there is NO supplied global sector/payment join.

The proposed all-finite-Jacobi global inverse-linear bound fails its N=2
diagnostic: the polynomial is proportional to x+a, where
a=(w+w^-1+w^3+w^-3)/4. For 1<a<=2, at x=a-2/a its invariant radial log
Hessian is -a^2/(4*(a^2-1)); a-1 is quadratic in 1-w. This is a rational
research calculation, NOT a new Lean obstruction. It does not refute a
cutoff-dependent Jacobi route or the original guarded character prefix:
their exact value/derivative deficits must be paid. Do not import this
diagnostic as a theorem about the original transfer or its physical gap.

### Observed paired-score evidence

Both final focused targets PASS, with all eight printed public dependencies
within {propext, Quot.sound}:

| Declaration | Source |
| --- | --- |
| `decomposable_plucker` | `lean/YMGap/Continuum/QuaternionHaarConditionalScorePairedFrame.lean:54` |
| `conditionalScore_firstJet_pin` | Same source `:70` |
| `conditionalScore_plucker` | Same source `:103` |
| `plusSquare_eq_sixScoreSquare` | Same source `:192` |
| `minusSquare_eq_sixScoreSquare` | Same source `:204` |
| `plusSquare_weighted_pin` | Same source `:216` |
| `minusSquare_weighted_pin` | Same source `:222` |
| `pairedScoreAngularBudget_eq_exact` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPairedScoreBudget.lean:66` |

Accepted logs, in this order:

```text
/private/tmp/ym-oct7-paired-score-frame-clean.log
ae6df76315d15b00b6d229ab0e9559cb037ab7633be643cd063bb5733e6fa4f0
/private/tmp/ym-oct7-original-paired-score-budget-clean.log
a1dc372e913053121744f42baa37fc4ebadb92626b2812e3b6014f0a16403007
```

The first frame compilation passed elaboration but FAILED the axiom gate:
private dependent finite-index congruences brought `Classical.choice` into
the energy identities. Intermediate axiom prints localized the dependency;
direct congruences at literal slots 0,1,2 removed it. The old and localization
logs are NOT accepted proof evidence. The initial original consumer also
failed on a missing defining namespace, subsequently supplied without changing
the statement. No new source sorry/axiom/classical input or limits change.
Fresh preflights before every launch showed no competing compiler, 87--88%
free and zero swap; checks ran sequentially with one 20-GiB worker and 12-GiB
reserve. Root registration only; no full-root/tree audit or baseline refresh.

Decision: CONTINUE with the exact three-score currency, NOT a geometric or
Harnack claim. The energy conversion is now proved for the original budget,
including zero/arbitrary sources and signed multipliers. Constructive frame/
heat identification, the genuine one-sided bound, actual conditional law,
normalization, retained signed cost and all scaling/Clay joins remain OPEN.
The user's lattice-measurement note remains incorporated in the existing
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and work-plan priority;
it supplies no numerical premise for this proof. No routine listing scan or
duplicated literature review was needed. The canonical broad chart is unchanged.

Independent read-only source review found no semantic issue: each triple
alone retains the original six-score energy without a radius/factor-two
correction, and the actual consumer adds no source-support, nonzero-source
or positive-sigma premise. It confirms the algebra-versus-geometric-curvature/
conditional/scaling boundary; the review itself is not compilation evidence.

## Next experiment: actual paired scalar jets and global transverse producer

The previous checkpoint is PROGRESS: `71419b7c` supplies checked original
score/budget equalities and is pushed to main. This continuation preserves the
unchanged Clay objective and the original action. Two bounded mathematical
tasks meet at the relative scalar, rather than growing cap-only wrappers.

1. Prove actual paired second scalar jets on blocks 0/1: Ji^2(x)=-x and
   JiJj(x)+JjJi(x)=0 for distinct directions, hence the frozen polynomial
   contraction is -(sum ui^2)*x. Available inputs: the literal relative scalar,
   supported angular carrier differentiation and finite canonical checks.
   Coefficients ui must not be differentiated. Arbitrary-block recoding and
   a geometric heat/PDE identification are separate, not implied by this pin.
2. Construct a GLOBAL one-sided transverse polynomial certificate for the
   literal Jacobi heat h and its ACTUAL formal scalar derivative h_x:

       C_T*h^2-x*h*h_x >= 0,   C_T=2*w/(1-w^2).

   No density-floor reciprocal belongs in C_T. The full interval is covered
   by the exact affine identity, with c=w^(2k+1):

       f-x = ((c^2+2c)*(1+x)+((c-1)^2+1)*(1-x))/2,
       f=1+2*c*x+c^2.

   Retain the Euler factor. Simultaneous positive product/derivative
   induction adds 2*c at each factor; the finite geometric sum is bounded by
   C_T. Use the actual QPoly formal derivative and coefficient identities,
   not merely a recursively defined jet. Initial empty/constant heat cases,
   x=+/-1, full signed x and the normalization are decisive checks.

The second target is an actual partial curvature producer, NOT a global
matrix lower bound: the negative-hemisphere radial mixing inequality remains
unsupplied. The scalar certificate's angular/substitution pin, exact weighted
character join, and transport to the original UNWEIGHTED prefix must be
proved before an original transfer estimate is claimed. Existing absolute
deficits may use the heat floor in their tighter CUT OFF tolerance without
placing its reciprocal in the final curvature cost; the current cutoff alone
does not supply that transport. No global hemisphere assumption is allowed.

Sol implements the bounded leaves; root serializes focused verification,
using one 20-GiB worker, 12-GiB reserve and a fresh dynamic preflight at every
launch. Revise if the actual derivative pin is absent, finite cutoffs or
unit-radius endpoints are dropped, or a full radial/matrix result is inferred
from the transverse leg. No new hypothesis bundle, canonical field change,
routine literature scan or chart reprint is planned.

### Observed scalar-jet and transverse evidence

Both final focused targets PASS. All fourteen printed public dependencies
are exactly {propext, Quot.sound}; no new source sorry/axiom/classical input.

| Declaration | Source |
| --- | --- |
| `pairedScorePlus_zero_derivative_pin` | `lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:54` |
| `pairedDerivative_carrier` | Same source `:90` |
| `relativeScalar_supported` | Same source `:105` |
| `relativeScalar_second_jet` | Same source `:129` |
| `relativeScalar_mixed_jet` | Same source `:139` |
| `frozenScalarSecondJet_pin` | Same source `:212` |
| `frozenScalarSecondJet_weighted_pin` | Same source `:243` |
| `product_formal_derivative_pin` | `lean/YMGap/Continuum/JacobiHeatTransverseCurvature.lean:112` |
| `factor_transverse_certificate` | Same source `:185` |
| `productDerivative_transverse_certificates` | Same source `:234` |
| `transverseCap_denominator_pin` | Same source `:289` |
| `transverseCap_nome_defect_le_one` | Same source `:301` |
| `transversePrefixCost_le_cap` | Same source `:319` |
| `heat_transverse_curvature_certificate` | Same source `:334` |

Accepted logs and SHA-256:

```text
/private/tmp/ym-oct7-paired-scalar-jets-final.log
a1af551a8ae2d384203dd16b7411f9128c2de5af78a6384bf48e7a816f984b5e
/private/tmp/ym-oct7-jacobi-transverse3.log
6dbf688f5c492008d7f0bc43ff312f27415bade37d5ab1e2696318af0ebab4d6
```

The earlier transverse logs are FAILED elaboration, not accepted evidence.
Repairs used named coefficient negation, explicit polynomial/constant
arguments and exact finite-sum normalization; no mathematical hypothesis
changed. Fresh preflights before each launch showed no competing compiler,
87--88% free and zero swap. Verification was serialized with one 20-GiB
worker and 12-GiB reserve. Root import registration only; no full-root/tree
build, full axiom audit or baseline refresh was run.

Independent read-only source review found no material issue: actual second
jets precede multiplication by frozen u, interval certificates retain both
1+x and 1-x, and the formal derivative/Euler/normalization pins are literal.
Its review was not compilation evidence. No geometric group flow, covariant
matrix Hessian, original unweighted heat, OS norm or physical gap is claimed.

Decision: CONTINUE. The transverse coefficient has the desired inverse-linear
nome-defect scale, unlike the prior constructed entrywise cap. The negative-
hemisphere RADIAL mixture is the substantive missing estimate. With
r_k=2*c_k/(1+2*c_k*x+c_k^2), c_k=w^(2*k+1), S_m=sum r_k^m, the still-unproved
denominator-cleared radial target is

```text
C*S1^2 >= (1-x^2)*(S2*S1^2-2*S3*S1+S2^2)
              + x*(S1^3-S1*S2),   C=O(1/(1-w)), N>=N0(w).
```

This is a research target, not a new Lean premise or assertion of an available
cutoff N0. The N=2 diagnostic above prevents claiming it for all finite N.
Scalar substitution/angular heat pins, arbitrary-block recoding, exact
weighted-character derivative transport and the original unweighted cutoff
join must also be established before an original conditional matrix estimate.
Complete signed cost, normalization, independent survival, completed
comparison, physical/volume control, SAME limiting QFT and every-group/Clay
requirements remain OPEN. Supporting proofs change none of the canonical
chart's displayed broad claims; no chart is reprinted.

The current pasted note
`/Users/darthur/.codex/attachments/cf965d8e-085c-42c2-a303-16f0ae70d860/Pasted text.txt`
was read against the existing lattice-mass research audit and work-plan
priority. Its useful numerical-channel versus physical-generator distinction
is already incorporated there, together with finite-spacing and regularity
corrections. No measured mass, transfer/Hamiltonian identification or continuum
regularity hypothesis was imported into these certificates; no duplicate
paper review or routine listing scan was performed.

### Radial experiment selection: retain the product/mixture cancellation

Independent bounded mathematical review supplies a decisive endpoint screen,
checked algebraically by root but NOT yet a Lean theorem. At x=-1 and N>=1,
set r0=2*w/(1-w)^2. Pairing the terms of the finite geometric sum gives

```text
1-w^(2k+1) >= (2k+1)*w^k*(1-w),
r_k(-1) <= r0/(2k+1)^2,
sum_(k=1)^(N-1) 1/(2k+1)^2 <= sum 1/[4k(k+1)] <= 1/4.
```

Thus S1<=5*r0/4 and S2>=r0^2, so S2/S1>=4*r0/5. The COMPLETE radial
endpoint is S1-S2/S1>=0 since S1^2>=S2; however the isolated mixture
contribution is -S2/S1, necessarily of inverse-quadratic nome-defect size.
This persists at arbitrarily large finite cutoffs. Separately imposing
inverse-linear floors on product and mixture therefore cannot prove the
desired joined bound. PRUNE that split, NOT the full radial/onset target,
the original action, or Yang--Mills. The next producer must retain their
cancellation (and the radial positive-mixture variance); no premise or
canonical frontier field changes. This screen is mathematical research
evidence, kept distinct from the fourteen kernel-checked gates above.

## Next bounded experiment: contract radial mixture to product curvature

Root verified the exact scalar cancellation, but no Lean result is yet claimed
in this section. Put a=1-x^2, D=a*S2+x*S1, with S_j the finite r-power sums.
The cleared radial numerator is exactly

```text
Lnum = -(S1^2-S2)*D + 2*a*(S1*S3-S2^2).
C*S1^2+Lnum = (C-D)*(S1^2-S2)+C*S2+2*a*(S1*S3-S2^2).
```

Available constructive finite inputs: r_i>=0, so S1^2-S2>=0 and
S1*S3-S2^2>=0, the latter by weighted squared pair differences. Thus a>=0,
C>=0 and the PRODUCT bound D<=C suffice. No reciprocal S1 or heat floor is
needed, and the empty prefix is included. The direct consumer is the radial
research target above; this is a strictly sharper mathematical reduction,
not an assumed original gap or new frontier bundle.

Sol implements the finite rational identities/positivity; root alone runs the
focused 20-GiB check after a fresh preflight. An independent read-only review
locates the exact remaining same-product Gaussian/second-derivative input.
Predicted outcome: finite cancellation contracts; the Poisson/curvature input
remains open. Revise if any moment is not the actual finite prefix, positivity
is silently assumed instead of proved, a division excludes zero prefixes, or
a Poisson equality/physical time is inferred from the algebra. Auxiliary
circle time t_theta=-log(w) must not be identified with the carrier time
-4*log(w) or standard g^2=-8*log(w). No geometric or continuum closure.

### Narrow analytic route, without importing a classical premise

The underlying P(w,cos(theta)) is the theta3 product at angle theta/2, not
the SU(2) derivative heat itself. The product normalization and modular
transformation are classical benchmarks in
[NIST DLMF 20.5.3](https://dlmf.nist.gov/20.5.E3) and
[20.7.32](https://dlmf.nist.gov/20.7.E32). Root's inference from those formulas:
for auxiliary circle time t_theta=-log(w), P is proportional to the positive
wrapped Gaussian sum G=sum_j exp(-(theta-2*pi*j)^2/(4*t_theta)). Its cleared
log-Hessian is -G^2/(2*t_theta) plus a nonnegative weighted variance. This
suggests D_infinity<=1/(2*t_theta), NOT an imported constructive theorem.

For a cutoff with w^(2*N+1)<=1/8, the negative product tail costs at most
sum_(k>=N) r_k<=8*w^(2*N+1)/(1-w^2)<=1/(1-w). Together with
t_theta>=1-w this suggests C=3/[2*(1-w)] for the finite joined radial
expression. These are research estimates pending actual derivative, tail
and limit proofs, not an available physical bound or established Lean cutoff.

The needed analytic join is specifically the SAME theta3 PRODUCT's Gaussian
identity and first/second angular derivative control with explicit moduli.
Do not unnecessarily demand a full SU(2)/Faraut image formula or its sine-
denominator endpoint removal: h is reached through finite algebra instead.
Existing `JacobiTripleProductOnBox.thetaProduct_eq_fullThetaSeries`
(`lean/YMGap/Continuum/JacobiTripleProductOnBox.lean:91`) already identifies
the all-nome on-box product with the normalized cosine series. It does not
prove the Poisson/Gaussian or second-derivative join. `JacobiModularCReal`
explicitly withholds modular inversion, and the Faraut image formulas remain
supplied inputs. No classical source is added as a Lean axiom or hypothesis;
angle/carrier, finite-to-limit and physical-time identifications stay OPEN.

### Observed finite radial cancellation evidence

The final focused target PASSes all seven gates within {propext, Quot.sound}.
The first three moment nonnegativity theorems use propext only.

| Declaration | Source |
| --- | --- |
| `M1_nonneg` | `lean/YMGap/Continuum/JacobiHeatRadialMixtureCancellation.lean:50` |
| `M2_nonneg` | Same source `:54` |
| `M3_nonneg` | Same source `:57` |
| `first_square_gap_nonneg` | Same source `:63` |
| `moment_variance_nonneg` | Same source `:112` |
| `radialNumerator_cancellation` | Same source `:157` |
| `radialMixture_payment_nonneg` | Same source `:177` |

Accepted log and SHA-256:

```text
/private/tmp/ym-oct7-radial-mixture2.log
0abeaf288548027f0a0b4267a1c4bde6a26a75dfa1be4382f716ca65c07d7f0d
```

Initial elaboration failed on a missing convenience congruence, unreduced
empty-prefix goals and a function-pattern layout. Root used the core rational
congruences and explicit empty reduction; no hypotheses changed. No source
sorry/axiom/classical input. Both preflights showed no competing compiler,
87--88% free and zero swap; one 20-GiB worker, 12-GiB reserve. No full-root/tree
build/audit or baseline refresh. This is finite rational algebra, not yet an
actual angular heat inequality.

Independent read-only review confirmed the actual moment sums, constructed
variance/pair positivity, empty case and full signed numerator/payment. It
also confirmed the narrower missing theta3 circle-Gaussian bridge: no full
SU(2) Faraut sine-denominator formula is needed for this route. The review
itself is not compilation evidence.

Decision: CONTINUE from the PROVED finite reduction to a genuine product
curvature producer and SAME heat-jet/cutoff/conditional joins. No separated
mixture floor, global density-floor cost, or classical Poisson premise is
introduced. The finite derivative/moment identifications, Gaussian derivative
limits, useful original signed cost, scaling, independent survival, completed
comparison and all physical/continuum/Clay obligations remain OPEN. Together
this continuation checks three focused leaves and twenty-one public gates,
without changing any canonical displayed broad claim. No chart reprint.

## Next experiment: actual radial heat/moment jet join

Previous checkpoint `75075d27` is verified PROGRESS and pushed to main.
The finite radial algebra must now refer to actual Jacobi derivatives before
it is a heat estimate. For r_i=HKConv.sTerm(w,x,i), retain the same full
Euler-weighted product P and normalized heat h=(inverseNome/2)*P'_x.
Prove the actual FORMAL first three product jets at 1+x:

```text
P'   = P*S1,
P''  = P*(S1^2-S2),
P''' = P*(S1^3-3*S1*S2+2*S3).
C*h^2+(1-x^2)*(h*h_xx-h_x^2)-x*h*h_x
     = (inverseNome*half*P)^2*(C*S1^2+Lnum).
```

Consumer: `JacobiHeatRadialMixtureCancellation.radialMixture_payment_nonneg`.
Inputs already available are the literal shifted product/heat, formal
Leibniz rules, first-derivative normalization and factor/sTerm cancellation.
The output is an ACTUAL finite scalar heat implication given the smaller
PRODUCT ceiling; it does not produce that analytic ceiling. Empty/constant
prefixes, x=-1, full signed x and the normalization are decisive tests.
No derivative is freely supplied in lieu of formal differentiation.

Sol implements the bounded actual-jet leaf, root checks it with one 20-GiB
worker and 12-GiB reserve after a fresh dynamic preflight. A parallel math
review seeks a shorter signed product ceiling without insisting on a full
Poisson formalization; another reviews the later Haar-certificate join.
Revise if only recursive free jets are pinned, any factor/normalization is
dropped, a zero case is excluded, or pointwise order is silently treated as
Haar-square/conditional/OS order. No new frontier bundle or field weakening.

The eventual polynomial certificate route may use the cleared identity
`P*Lheat=P''*Qproduct+C*P*(P'^2-P*P'')+2*(1-x^2)*P^3*variance`.
Its positivity and positive-multiplier removal must themselves be constructed
under arbitrary original action insertions; this paragraph is a research
target, not that missing proof. No chart claim changes from selecting it.

### Observed outcome: ACTUAL finite heat-jet join checked

The experiment succeeds at its stated scalar scope. All nine load-bearing
declarations in `JacobiHeatRadialMomentJets.lean` pass the focused check and
print exactly {propext, Quot.sound}. No elaboration retry or statement change
was needed. The public padded-coefficient evaluation bridge is reused.

| Declaration | Source |
| --- | --- |
| `product_derivative_coeff_pin` | `lean/YMGap/Continuum/JacobiHeatRadialMomentJets.lean:130` |
| `product_first_moment_pin` | Same source `:142` |
| `product_second_moment_pin` | Same source `:149` |
| `product_third_moment_pin` | Same source `:175` |
| `heat_eval_moment_pin` | Same source `:214` |
| `heat_first_moment_pin` | Same source `:226` |
| `heat_second_moment_pin` | Same source `:242` |
| `heat_radial_moment_pin` | Same source `:265` |
| `heat_radial_nonnegative_of_productCost` | Same source `:305` |

Accepted log and SHA-256:

```text
/private/tmp/ym-oct7-radial-moment-jets1.log
ba78f37d8dd70c8a081efe89bd38818a1382990b06a7cc3a160bb334fa333a9b
```

Root read the complete source; independent read-only review confirmed actual
formal pderiv through order three, literal sTerm/factor cancellation, repeated
index terms, inverseNome*half normalization, and empty/constant prefixes.
The final expression consumes exactly C>=0, x^2<=1 and actual D<=C. No heat
or moment density is inverted. This closes the scalar heat/moment pin missing
from checkpoint 75075d27; it does NOT produce the product ceiling.

Fresh escalated preflight found no competing compiler, 88% free and zero
swap. One capped 20-GiB worker, 12-GiB reserve; no full-root/tree build/audit
or baseline refresh. The root import is registered, not a full-root check.
No new sorry/axiom/classical input or canonical frontier change. Broad chart
unchanged; no reprint.

### Parallel product-ceiling and certificate review

These are mathematical/source reviews, not new Lean evidence. For the
negative hemisphere the elementary signed summand
F(s)=(1+x*cosh(s))/(cosh(s)+x)^2 has integral one. For -1<x<0 it has a
single negative minimum and total variation at most 3/[2*(1+x)]. Midpoint
quadrature would bound the infinite sum by 1/(2*t_theta)+3/[4*(1+x)],
giving an inverse-linear nome-defect ceiling when 1+x>=1-w. At
x<=-2*w/(1+w^2), every finite summand is nonpositive. This leaves the strip
`(1-w)^2/(1+w^2) < 1+x < 1-w`; its width is not a payment under the
original action. No global elementary summed bound was found.

A fixed-multiplier termwise telescoping shortcut fails: at w=1/2,c=1/8,
the comparison using g(c)=(1-c^2)/(1+2*c*x+c^2) would require K>=85/81
at x=1 and K<=45/49 at x=-1. This rejects that particular comparison,
not the summed target or Yang--Mills. Retain signed corrections or use the
genuine theta3 Gaussian bridge.

The prospective cleared polynomial identity and pair-variance exponent 3
were independently confirmed. Existing square-certificate multiplication,
positive-coefficient substitution and positive-window order reflection can
retain overlapping variables and a certified original action weight. The
missing analytic producer is a SAME finite Certificate for
`Qproduct=C*P^2-(1-x^2)*(P'^2-P*P'')-x*P*P'` with useful nome dependence.
Scalar pointwise positivity is not such a certificate. Positive-multiplier
reflection cancels only in a Haar expectation; it does not assert polynomial
certificate division. An actual action weight must also be certified before
it is used in that construction.

Decision: CONTINUE from the checked actual heat-jet reduction to that genuine
product-ceiling producer and its Haar/conditional join. Do not extend wrappers
that re-assume it, split away the mixture variance, or identify the auxiliary
circle clock with physical time. Explicit angular/cutoff/limit transport,
useful original signed cost, scaling, independent survival, completed
comparison and all physical/continuum/Clay obligations remain OPEN.

## Next experiment: theta addition square and signed finite cutoff

Checkpoint a71313a4 is verified PROGRESS and pushed to main. The next
producer remains the useful SAME-product radial ceiling, not another
consumer that assumes it. Root found a shorter algebraic candidate than
Poisson/modular inversion; two independent mathematical screens confirm
the sign and constants. This section is a DERIVATION/PLAN, not Lean evidence.

### The addition square, without a Gaussian or physical-clock premise

Use [DLMF 20.7.8](https://dlmf.nist.gov/20.7.E8), together with
[20.7.2](https://dlmf.nist.gov/20.7.E2) and
[20.7.4](https://dlmf.nist.gov/20.7.E4). Multiplying E8 by theta3(0)^2,
substituting E2 for theta4(z)^2, and substituting E4 for the remaining
theta2/theta3 difference gives, after positive theta4(0)^2 cancellation,

```text
g0^2*g(z+u)*g(z-u) = g(z)^2*g(u)^2 + theta1(z)^2*theta1(u)^2,
g(z)=theta3(z,w), g0=g(0).
```

E8 is not verbatim this identity; the conversion is essential. An alternate
pure-convolution derivation uses [Watson E13/E14](https://dlmf.nist.gov/20.7.E14)
and the elementary dot-product/determinant square identity. Splitting a
bilateral double sum by equal parity under (m,n)->(m+n,m-n) is the proposed
constructive proof; reindex the finite domain and bound its boundary before
passing to the limit. Literal same-N truncated theta sums do NOT satisfy
the infinite addition identity exactly.

Twice differentiating in u at zero gives

```text
g0^2*(g*gzz-gz^2) - g0*gzz(0)*g^2 = theta1'(0)^2*theta1(z)^2 >= 0.
```

For x=cos(2z), the angular logarithmic curvature is -4*D_infinity(x).
Hence the derived ceiling is

```text
D_infinity(x) <= D_infinity(1)
              = sum_i 2*c_i/(1+c_i)^2
              <= C_T = 2*w/(1-w^2) <= 1/(1-w).
```

No limiting curvature, addition identity or differentiated equality is
currently a produced Lean input. Existing product/cos-series equality alone
does not supply them. The auxiliary argument is not physical time.

Fractional powers, sine coordinates and elliptic functions need not be
introduced into the rational cleared target. Put

```text
R_n(x) = 1 + 2*sum_{k=1}^n T_k(x),
A(x) = sum_{n>=0} (-1)^n*w^(n*(n+1))*R_n(x),
B    = sum_{n>=0} (-1)^n*(2*n+1)*w^(n*(n+1)).
P0^2*[D0*P^2-(1-x^2)*(P'^2-P*P'')-x*P*P']
      = 2*w*(1-x)*A(x)^2*B^2,
P0=P(1), D0=P'(1)/P0.
```

This is the same square after eliminating theta1's quarter-nome and
half-angle factors; its sign and factor two were independently checked.
For the FULL Euler-weighted product, P=1+2*w*x+O(w^4); no spurious w^2
term is retained. Needed new proof: actual convergent parity convolution,
the appropriate formal derivative/limit pins and explicit tail moduli.

### The independent finite tail producer

For the ACTUAL rational factor r_i=2*c_i/(1+2*c_i*x+c_i^2), retain
d_i=(1-x^2)*r_i^2+x*r_i. On [-1,1], the proposed exact cleared identity
`factor_i^2*(r_i-d_i)=2*c_i*(1-x)*(1-c_i)^2` proves d_i<=r_i;
d_i+r_i>=0 proves the other sign. At c_N<=1/8, each tail denominator
is at least 1/2, so r_{N+j}<=4*c_N*(w^2)^j and an explicit sufficient
finite-to-finite error is E_N=4*c_N/(1-w^2), with
`(1-w)*E_N<=1/2`. Combined with the ADDITION ceiling, this would give
`D_N<=3/[2*(1-w)]`. This does not assume finite-product monotonicity.

Sol implements that bounded actual signed-tail leaf; root alone compiles
with one 20-GiB worker and 12-GiB reserve after a fresh dynamic preflight.
Its immediate consumer is finite cutoff transport of the addition-square
ceiling to the actual jets in JacobiHeatRadialMomentJets. Revise if the
sign of omitted terms is lost, positivity of the denominator is assumed
without proof, the cost includes an original heat-floor reciprocal, or an
infinite identity is claimed for literal finite truncations.

### The strict scalar-to-Haar join already has an actual consumer

Root read `QuaternionHaarBernsteinRowCertificate.strictPolynomialCertificate`
(`lean/YMGap/Continuum/QuaternionHaarBernsteinRowCertificate.lean:205`): an
explicit STRICT rational interval margin computes a Bernstein cutoff/row
and an exact original Haar square certificate, with no loss in the target
polynomial. `QuaternionHaarUnitIntervalCoordinate.unitArgument_certificate`
and `oneMinusUnitArgument_certificate` supply its actual coordinates from
a constructed unit square bound.

After the missing addition ceiling and checked tail, choosing
C=2/(1-w) leaves slack delta=1/[2*(1-w)]. The finite product's explicit
positive lower bound ell_N=product_i Euler_i*(1-c_i)^2 would give
`Qproduct >= ell_N^2*delta`. That margin, not a mere non-strict sign,
is the required input to the EXISTING Bernstein producer. A small ell_N
may enlarge its approximation modulus; its reciprocal is NOT placed in
the curvature coefficient. Then retain any certified overlapping original
action by certificate multiplication and use the existing positive-window
Haar order reflection for positive multipliers. This join still needs the
actual interval margin, product lower bound and original-action instantiation.

Decision: REVISE analytic selection toward the shorter addition-square
producer; retain Poisson as an alternative, not an extra required obstacle.
No new bundle, weakened canonical field, classical premise, chart closure
or physical mass claim follows from this research selection.

## Observed proof increment: actual signed radial limit and cutoff transport

The finite-tail experiment succeeded. Root read both full new sources;
independent Sol mathematical review found no material sign, constant or
scope defect. This section records kernel evidence, separately from the
addition-square research above.

- `lean/YMGap/Continuum/JacobiProductRadialSignedTail.lean:60`,
  `radialSummand_sum_pin`, pins the literal signed sum to the actual
  `productRadialCost`. At line 72, `radialSummand_bounds` proves
  -r_i<=d_i<=r_i on the FULL interval. Its exact cancellation is
  f_i-(1+x)*2*c_i=(1-c_i)^2; no sign of d_i is discarded.
- At line 148, `sTerm_tail_le_four_geoAmp` uses c_N<=1/8, hence each omitted
  denominator >=1/2, to prove r_(N+j)<=4*c_(N+j). At line 178,
  `sTerm_finite_tail_le` sums this against the actual geometric tail.
  At line 215,
  `productRadialCost_finite_tail_le` gives D_N<=D_(N+L)+E_N for every L.
- `radialTailPayment_denominator_pin` (line 238) and
  `radialTailPayment_nome_defect_le_half` (line 252) pin E_N*(1-w^2)=4*c_N and
  (1-w)*E_N<=1/2. The onset remains an explicit hypothesis; these theorems
  do not silently produce a cutoff or the infinite ceiling.
- `lean/YMGap/Continuum/JacobiProductRadialLimit.lean:131`,
  `productRadialCostCReal`, constructs the actual D_N sequence. At line 143,
  `productRadialCostCReal_approx` is rfl. `radialTolerance` (line 86) and
  `radialCutoff` (line 90) are Q'/Nat data; `radialCutoff_tail_le` (line 108)
  and `radialCutoff_cauchy` (line 168) prove the explicit convergence
  modulus, uniform in x at each named w. The legacy Prop modulus is filled
  from named data, never used to extract that data.
- `productRadialCost_le_limit_ceiling` (line 191) consumes a bound on THIS
  limit and transports it to D_N<=C+E_N using the signed finite comparison
  at max(N,M), then removes the rational precision error. Cstar(w) occurs
  only in convergence, not the finite ceiling coefficient.

### Exact verification boundary

One worker, mandatory 20-GiB ceiling, 12-GiB reserve. Fresh dynamic
preflights before each launch found 87--88% free memory, zero swap and no
competing Lean/Lake/pytest/runner processes. Root used only the monitored
launcher. The first signed-tail check failed on 0+j normalization, not
mathematics; an explicit Nat.zero_add rewrite repaired it without changing
any statement. Failed-check sorryAx output is NOT proof evidence.

Final focused checks, each emitting an olean:

```text
/private/tmp/ym-oct7-radial-signed-tail2.log
SHA256 ca3fd8e53c0b1ea6c2a4135851b321b387dfe5c2d6f7ad288700ac269305b3dd
7 printed gates pass, all within {propext, Quot.sound}.

/private/tmp/ym-oct7-radial-limit1.log
SHA256 3a61c927d2b771e3eb36f65770118dbd9cd4527b7a8bee60a2d6670bc289029c
10 printed gates pass, all within {propext, Quot.sound}.
radialTailPrefactor, radialTolerance and radialCutoff are axiom-free.
```

No full-root/tree build or audit, baseline refresh, new source sorry/axiom,
classical input or canonical field change. Root imports are registered;
this is not a full-root check. The canonical displayed claims remain open,
so the ASCII chart is unchanged and not reprinted.

### Continue: actual convolution, not another assumed-ceiling consumer

The addition/derivative-limit ceiling is the missing producer. Independent
research review spells out the finite geometry: (m,n)->(m+n,m-n) has an
even class m=j+k,n=j-k and odd class m=j+k+1,n=j-k. The exponent pins are
2*j^2+2*k^2 and 2*j*(j+1)+2*k*(k+1)+1. The original |m|,|n|<=N box becomes
the even |j|+|k|<=N diamond or the odd half-shifted diamond, NOT the whole
containing rectangle. For either class, omitted shells T>=N+1 have at most
4*T points, exponent >=T^2 and second-angular weight <=4*T^2; proposed
error is bounded by 16*sum_(T>=N+1) T^3*w^(T^2). These statements are
RESEARCH until the exact finite reindex/tail producer is checked.

Root also read the whole existing `ThetaProductStrictFloor.lean`:
`floor_le_Ppart` (line 91) supplies a positive floor for the ACTUAL
Euler-weighted finite product, uniform in x,N at each named nome;
`thetaConvCRealGen_geRat_floor` (line 101) covers its existing completion.
Thus a new floor module is unnecessary. With a genuinely produced ceiling
and strict slack delta, Qproduct>=delta*floor(w)^2 would feed the EXISTING
Bernstein producer. This affects the certificate modulus, not the curvature
constant. No strict margin/Haar/action certificate is claimed here.

Decision: CONTINUE the shorter addition-square producer with bounded finite
reindex work and independent mathematical review. Retain derivative-limit,
original weighted conditional/scaling and all downstream Clay obligations.

## Observed proof increment: finite addition-route producers

The next bounded experiments also supply actual objects/estimates rather
than another assumed-addition consumer. Root inspected complete sources;
independent Sol reviews checked signs, zero/negative indices, normalizations
and the exact remaining scope.

- `lean/YMGap/Continuum/ThetaParityConvolution.lean:314`,
  `signed_box_parity_convolution`, proves the full arbitrary-weight finite
  signed-box equality to EVEN+ODD DIAMOND sums. `encode_decode` (line 46),
  `decode_encode` (line 68) and `boxParityDecode` (line 212) carry explicit
  inverse/boxed data. `even_frequency_pin` / `odd_frequency_pin` (73/79)
  and `even_exponent_pin` / `odd_exponent_pin` (85/93) retain both branches,
  including the odd exponent +1. The containing box N+1 is only an
  enumeration device; `evenDiamondIndices_mem` / `oddDiamondIndices_mem`
  (179/195) impose EXACT transformed original-box constraints. N=0 has one
  even cell and no odd cells. No rectangle substitution is claimed.
- `lean/YMGap/Continuum/ChebyshevHalfShiftProduct.lean:113`,
  `halfShift_product`, constructs the exact shifted kernel
  (1-x)*C_n*C_m=T_dist-T_(n+m+1), C_n=U_n+sinCoord n. `rotation_difference`
  (line 86) is proved from existing rotation addition and Pythagorean
  identities, on both index orders. Arbitrary rational x and zero indices
  are included; n=m=0 gives 1-x. This supplies finite algebra for the
  independent shifted/alternating convolution, not that completed identity.
- `lean/YMGap/Continuum/JacobiProductRadialEndpoint.lean:31`,
  `productRadialCost_at_one_pin`, gives the ACTUAL D_N(1)=M1. At line 40,
  `endpoint_sTerm_le_rate` uses the actual denominator 1+2*c+c^2>=1.
  `productRadialCost_at_one_le_cap` (54) and
  `productRadialCostCReal_at_one_le_cap` (65) therefore produce the useful
  endpoint ceiling C_T=2*w/(1-w^2), on every prefix and the SAME constructed
  limit. The whole-interval comparison D_infinity(x)<=D_infinity(1) is NOT
  supplied. No heat-floor reciprocal enters this ceiling.
- `lean/YMGap/Continuum/ThetaAngularShellTail.lean:87`,
  `shellTerm_succ_le_half`, proves the actual shell 16*T^3*w^(T^2)
  contracts by half after `shellOnset` (line 34). The constructive onset
  max(1,powBaseCutoff(w,1/16)) forces w^(2*T+1)<=1/16, and cubic growth
  costs at most 8. `shellTail_le_two` (line 135) bounds every finite tail
  by twice its first shell. `shellTolerance` (161), `shellTailCutoff` (165)
  and `shellTail_le_epsilon` (192) retain explicit rational/Nat data paying
  epsilon at every later index. The angular shell count and domination
  of actual convolution errors are still missing joins, not hypotheses
  silently discharged by this scalar leaf.

### Exact verification boundary

Same monitored one-worker policy and fresh dynamic preflight at EACH launch:
87--88% free memory, zero swap, no competing compiler/test/runner process;
mandatory 20-GiB worker ceiling and 12-GiB reserve. Final focused evidence:

```text
/private/tmp/ym-oct7-theta-parity2.log
SHA256 95021dc5c73842ad76f11b33363e4cd54771127527bde5de47e18543666a796e
13 public printed gates pass in {propext, Quot.sound}.

/private/tmp/ym-oct7-radial-endpoint1.log
SHA256 d1701accb555e21641cc8b4d92d4e05159fb1b931476cf292e9edb4934007f75
4 public printed gates pass in {propext, Quot.sound}.

/private/tmp/ym-oct7-halfshift1.log
SHA256 e19bbddd4f8e8c3e8a5d7ddcb08f8439184f367d2460780bbeb39d3740e21627
5 public printed gates pass; natDist and halfShiftCoord are axiom-free.

/private/tmp/ym-oct7-angular-shell4.log
SHA256 3f78f9bb909c75c73626d150f425e801021960e2f7919291a231709d360c9f69
8 public printed gates pass; shellTerm, shellOnset, shellTolerance and
shellTailCutoff are axiom-free.
```

The first parity check failed map-lambda typing, diamond decidability and
hidden-definition transport; the statements were unchanged in repair.
Static review removed a false UNUSED arithmetic equality before any shell
compile. Initial shell checks failed imports, unsupported tactic, lambda/
parenthesis parsing and explicit-argument normalization; the final source
passes. Failed-check sorryAx output is not evidence. No source sorry/axiom,
classical input, canonical field change, baseline refresh or full-root/tree
check/audit. Imports are registered without claiming full-root verification.
The displayed canonical goal claims remain open, so there is no chart reprint.

### Narrower mathematical join selected (RESEARCH, not a proved identity)

Use normalized half-nome series without square roots:

```text
E(x)=1+2*sum_(n>=1) w^(2*n*n)*T_(2*n)(x),
H(x)=sum_(n>=0) w^(2*n*(n+1))*T_(2*n+1)(x),
P(x)^2=E(1)*E(x)+4*w*H(1)*H(x),
K(x)=E(1)*H(x)-H(1)*E(x).
```

The coefficient is 4*w, not 2*w. After the still-missing actual convergent
convolutions, the elementary determinant square yields

```text
P(1)^2*(E(x)*E(y)+4*w*H(x)*H(y))-P(x)^2*P(y)^2
  =4*w*K(x)*K(y).
K(x)=(x-1)*A(x)^2, K'(1)=B^2, B=A(1).
```

Only the endpoint first scalar jet in y is needed. Its actual finite joint
kernel is the signed-box weight
w^(m^2+n^2)*T_|m+n|(x)*T_|m-n|(y). The endpoint derivative has weight
(m-n)^2; completing that convolution would give
E(x)*E'(1)+4*w*H(x)*H'(1)=2*D_infinity(x)*P(x)^2.
The differentiated determinant then gives the originally proposed square
2*w*(1-x)*A(x)^2*B^2. Independent mathematical reviews confirm these signs
and factors. Neither of the completed equalities is a Lean input yet.

Available first-derivative bridge inspected by root in full:
`lean/YMGap/Continuum/FiniteJacobiDerivativeComparison.lean:252`,
`fullProdDx_sub_two_dPartial_close`, already supplies the actual finite
Jacobi FIRST-jet comparison with explicit cutoff. Reuse it. It does not
supply the combined second-jet deficit required by D. Existing
`lean/YMGap/Continuum/ChebUDClosure.lean:389`, `udClosure`, supplies the
scalar Chebyshev angular ODE; the finite second formal-jet pin and weighted
coefficient comparison remain necessary. No general angular calculus or
Poisson/modular detour is imposed.

Decision: CONTINUE by specializing the checked finite reindex to actual
theta/jet weights, proving diamond-to-rectangle shell domination, and
composing SAME series limits. Then prove the shifted/alternating square and
the actual combined jet comparison. The endpoint ceiling and signed finite
tail are now produced, so the residue is smaller. Do not replace the missing
join by a theta-addition premise, identify each finite truncation with the
limit, or infer a Haar/conditional/physical gap from these scalar lemmas.

## Next bounded experiment: actual combined angular Jacobi comparison

Exact proposition: the literal Euler-weighted polynomial's angular jet
`(1-x*x)*P''-x*P'` approaches the corresponding bare theta angular sum,
with a computed cutoff uniform in x on [-1,1] at each named nome. This
removes the combined second-jet comparison input from the addition-route
radial ceiling; it does not itself prove the addition identity or ceiling.

Available inputs: `FiniteJacobiIdentity.Ppart_eq_finiteJacobi` is an
all-rational finite equality; `ChebyshevFormalJets` pins both ACTUAL formal
jets and `(1-x*x)*T_n''-x*T_n'=-n*n*T_n`. Constructive coefficient reflection
can lift the all-point finite equality before differentiation. Unit-slope
affine translation is still needed to identify the already-used shifted
product jets. The actual coefficient deficit is controlled by
`FiniteJacobiSeriesComparison.coefficientError_succ_le_gaussian`; the
existing `FiniteJacobiDerivativeComparison.shiftedGaussian_le` absorbs
the same quadratic frequency factor, without estimating T_n'' separately.

Prediction/test: the whole angular error has the existing explicit
`derivativeScale(w)*w^(2*N+1)` budget. Constant/empty order must give zero;
both endpoints must be included; nome dependence must stay explicit.
Verification: source review and serialized focused capped targets only,
no new general angular calculus or full-tree audit. Revise if the jet join
requires a substituted polynomial or an assumed second-derivative pin.

## Observed proof increment: actual angular comparison and finite endpoint jets

The selected combined second-jet comparison is now produced, not a supplied
premise. Completed additions, ceilings and physical joins remain open.

- `lean/YMGap/Continuum/ChebyshevFormalJets.lean:39`, `Tpoly`, is the actual
  first-kind coefficient recurrence. `eval_Tpoly_derivative` (130),
  `eval_Tpoly_second_derivative` (187) and `first_derivative_at_one` (199)
  pin both actual formal jets and T'_n(1)=n^2, including degree zero.
  `coefficients_of_eval_eqv` (163) constructively reflects all-rational
  evaluation equality into padded coefficients; `formal_angular_ode` (245)
  states the actual `(1-x*x)*T_n''-x*T_n'=-n^2*T_n` for every rational x.
- `lean/YMGap/Continuum/QPolyAffineJetTranslation.lean:31`, `translate`,
  reuses actual Horner composition with [c,1]. `eval_translate_derivative`
  (105), `derivative_coeff_pin` (122), `second_derivative_coeff_pin` (128)
  and `eval_translate_second_derivative` (133) derive both unit-slope jets.
  The existing shifted Jacobi product is retained, not replaced by a free
  derivative sequence or assumed chain rule.
- `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:143`,
  `product_series_coeff_pin`, reflects the ACTUAL Euler-normalized finite
  identity before differentiation. `productAngularJet_pin` (154) gives the
  exact whole angular series with -n^2 coefficients. The actual signed
  coefficient deficit is retained by `productAngularJet_sub_bare_pin` (188).
  `productAngularJet_sub_bare_le` (245) pays its whole error by the existing
  explicit `derivativeScale(w)*w^(2*N+1)`; `productAngularJet_sub_bare_close`
  (269) uses the existing Q'/Nat cutoff, uniform x on [-1,1] at named w.
  The quadratic Gaussian majorant suffices because the jets are combined,
  not separately estimated by fourth-degree frequency weights.
  `productRadialNumerator_pin` (288) proves
  `(1-x*x)*(P')^2-P*((1-x*x)*P''-x*P')=P^2*D`
  for the SAME literal product and HKConv.sTerm moments, without division.
- `lean/YMGap/Continuum/ThetaParityWeights.lean:119`, `thetaCell_even_pin`,
  and `thetaCell_odd_pin` (137) factor the actual cells, with exactly one
  odd w and natural exponents valid on negative indices. `theta_box_eq_diamonds`
  (202) and `frequency_box_eq_diamonds` (218) specialize the actual finite
  reindex. `thetaCellPolynomial_endpoint_derivative` (246) and
  `thetaSumPolynomial_endpoint_derivative` (282) now pin frequency weights
  to ACTUAL finite coefficient derivatives, including zero/empty cases.
  This is a scalar y-jet at y=1; no infinite/angle derivative is asserted.
- `lean/YMGap/Continuum/ThetaParityShellGeometry.lean:33`,
  `evenDiamond_iff_radius`, and `oddDiamond_iff_radius` (176) give exact
  domain geometry. `even_exponent_ge_radius_sq` (150) and
  `odd_exponent_ge_radius_sq` (339) give BOTH Gaussian exponent bounds;
  `even_frequencies_le_radius` (156) and `odd_frequencies_le_radius` (169)
  give the two caps. `oddRadius_eq_encoded_corner_max` (301) and actual
  encoded exponent pinning make the odd estimate a direct max-square bound.
  No shell count or actual weighted-sum domination is supplied yet.

### Exact verification boundary

All five final focused targets pass. Public printed gates stay within
{propext, Quot.sound}; computational definitions with gates are axiom-free.
No new sorry/axiom/classical premise, native_decide, field weakening, baseline
refresh or full-root/tree audit. Root imports are registered, not root-built.
Every launch used one 20-GiB worker, a 12-GiB reserve and a fresh process/
memory preflight; free memory stayed 85--88% and swap zero. No limits raised.

```text
/private/tmp/ym-oct7-chebyshev-formal-jets2.log
SHA256 b88bdde01eced69d595d6b58ae06979b431127d665e41a89ae10eb4150aba0c9
10 public printed gates; Tpoly and H are axiom-free.

/private/tmp/ym-oct7-affine-jet-translation1.log
SHA256 ff61d90241514337ea4ae32beeef96f636e72eb9b961c0df308a749e21c8887e
6 public printed gates; translate is axiom-free.

/private/tmp/ym-oct7-jacobi-angular-comparison3.log
SHA256 e5ecb234c27e180c06af1aa1a36dc25814b8ba2cc61e6230e210e0c20ee8b88e
13 public printed gates; five definitions are axiom-free.

/private/tmp/ym-oct7-theta-parity-weights3.log
SHA256 ec6afae30c81ea700993079e6682688e16dfac16181c716fba831bff719e836b
15 public printed gates; both cell/sum polynomial definitions are axiom-free.

/private/tmp/ym-oct7-parity-shell-geometry6.log
SHA256 f6406c6a9f2a49a75729aac9daa263338d0a5c59e28a7be48ffc0a32908d3628
8 public printed gates; all permitted.
```

Root inspected the complete final sources. Independent read-only mathematical
reviews found no substantive defect in actual jets, coefficient reflection,
angular signs, Gaussian budget, radial cancellation, parity weights and all
domain sign quadrants. Initial elaboration failures (casts, match layout,
recursion unfolding and a misplaced proof block) are not proof evidence.
The geometry initially elaborated with Classical.choice through omega on
conjunction goals; explicit conjunction introduction removed that dependency
in the final checked source. No such intermediate version is committed.

### Decision and smaller residue

CONTINUE: count the actual shells and pay omitted weighted sums, then compose
the actual diamond/rectangle series limits and shifted/alternating square.
The finite angular comparison and endpoint formal-jet producers are now
available. The raw Gaussian box's SAME-N endpoint jet belongs to bare F_N,
NOT finite Euler-weighted P_N: their completed identification still needs
the proved comparison and convergence joins. Never assert a per-N equality
between that box jet and `2*productRadialNumerator`.

Completed addition/whole-interval ceiling, strict Haar/weighted conditional
join, scaling/signed-cost estimates, independent survival, completed OS
comparison, physical/volume control, SAME limiting QFT, every group and Clay
remain OPEN. The displayed canonical claims have not changed, so no chart
reprint is warranted.
