# Adaptive directions at the original conditional-score frontier

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms,
and a finite strictly positive physical Hamiltonian mass gap.

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
