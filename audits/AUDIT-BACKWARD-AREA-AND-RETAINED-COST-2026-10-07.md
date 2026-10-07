# Decision: integrated response control and retained original cost (2026-10-07)

Whole-project goal remains OPEN: constructive nontrivial continuum Yang--Mills
on R^4 for every compact simple group, SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. No frontier fields or chart claims are changed.

## Propositions selected before verification

1. For the ACTUAL completed response R(k)=B(x,T^k x), e(k)=R(k)-R(k+1),
   form A(p,N)=sum_(i=0..N-1) R(p+i). Moment positivity and antitone e should
   give `2*N*R(p+N)+N*(N+1)*e(p+N) <= 2*A(p,N)`.
   Therefore `A(p,N)<=C*N*R(p+N)` gives `(N+1)*e(p+N)<=2*(C-1)*R(p+N)`.
   At p=side/2, N=side-p, this feeds the EXISTING `PathShiftedEpsBound`
   with c0>=4*(C-1), retaining the selected state and its completed norm.
   This is an integrated alternative to earliest-point window survival,
   not a supplied analytic bound on the AF family.
2. For original terminal a, source c, z=ell[a^2], p=ell[a*Ta],
   C=ell[c^2], Q=ell[c*Tc], D=p*C-z*Q and y=p*c-z*Tc, weighted
   Cauchy--Schwarz should give `C*Rem>=p*D^2` for the ACTUAL
   `Rem=p*ell[y^2]+z*ell[y*Ty]`. Insert into the existing exact cost
   recurrence without erasing the vacuum mismatch or any V factor.
   This retains a negative quadratic cost contribution, but supplies no
   scaling-useful transmitted-norm coefficient.

Inputs already written: `BF4WilsonAllNomeShiftedWindowSurvival.window_telescope`
and `window_energy_antitone`, the SAME mixed moment split/nonnegativity,
`BF4ExactSlabFixedSpatialRayleighCostTransport.clearedRayleighCost_transport_identity`,
actual weighted Cauchy--Schwarz and transfer positivity. Reuse them; do not
construct new interface/scorecard structures or assume initial small energy.

## Decisive tests and scope

A pure fast geometric response must NOT acquire a uniform side-scaled bound
from positivity or smoothing. A two-mode scalar test with both rates below one
will compare area C=6 with the old earliest-point survival at theta=1/11:
these are matching H1 constants c0=20, not unrelated tolerances. It is NOT an
original Yang--Mills state or a continuum counterexample. No uniform-family
strictness theorem is claimed merely from this finite test.

The cost estimate must handle C=0 without inversion, use the SAME spatial
weight/partitions, and keep signed mismatch. Abandon a proposed quantitative
consumer if it cancels a state norm, swaps ordinary L2 for the OS form, or
requires an unavailable action/center identification.

## Verification budget

Only the changed proof leaves and the small scalar decisive test, serialized
through the safe launcher: one 20-GiB worker, 12-GiB OS reserve and a fresh
dynamic capacity check per launch. Root alone compiles. Sol implements/reviews
bounded independent mathematics; no full build/audit or heartbeat increase.

## Observed result

Three focused targets PASS. The completed-area and original-cost inequalities
are constructed, not just specified. Every final printed axiom set is inside
{propext, Quot.sound}; the three finite rational comparison checks are axiom-free.
Earlier failed elaborations and their automatic sorryAx output are not evidence.
No source sorry, axiom, Classical input, native_decide, frontier-field change,
heartbeat/recursion-limit increase or full-root/tree build/audit was introduced.
The new scalar module is registered in the root import file; root registration
is not a root rebuild. Host preflights found no competing compiler, free-memory
percentage 87--88 and zero swap. Checks were serialized and completed in the
initial tool calls.

### Checked declarations and SAME-object joins

- `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedWindowSurvival.lean:288`,
  `windowResponseArea`: explicit finite RC data on the original completed vector.
  `:293`, `window_response_area_lower`: the unconditional integrated telescope.
  `:326`, `window_area_energy_bound`: cancellation of positive integer N only.
  `:347`, `window_area_epsBound`: endpoint H1 with c0>=4*(C-1).
  `:490`, `pathShiftedEpsBound_of_responseArea`: reaches the existing
  `PathShiftedEpsBound`, retaining literal `tr.state j`, `tr.response j`,
  schedule, width and normalization. The family-uniform area premise remains OPEN.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostTransport.lean:686`,
  `costTransportRemainder_terminal_square_lower`: p*D^2<=C*Rem from actual
  weighted Cauchy--Schwarz and transfer positivity, even when C=0.
  `:746`, `terminal_clearedRayleighCost_square_transport`: inserts this payment
  in the original recurrence, retaining signed z*q-v*p and literal V.
- `lean/YMGap/Continuum/BackwardResponseAreaStrictness.lean:43`,
  `moment_nonnegative`; `:60`, `finite_area_input`; `:63`,
  `earliest_point_survival_fails`; `:67`, `finite_H1`; `:71`,
  `pure_fast_H1_fails`. Final scalar test: S=32,p=N=16,C=6,c0=20,
  theta=1/11,q=63/64,a=1/2,fast amplitude=1048576. S>c0, so this H1
  is not automatic from e<=R. It demonstrates ONE finite premise separation,
  not a uniformly strictly weaker premise relation or an original YM instance.
  The pure fast mode fails c0=20 H1 at S=64; its proof is algebraic rather
  than a recursion-limit increase.

The original moment consumer for the next area estimate already exists:
`lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.lean:326`,
`smoothedResponse_orbit_expand`, and `:341`, `smoothedResponse_pin`.
Do not substitute an unrelated scalar response into this producer.

### Denominator consistency check (paper calculation, not a new Lean theorem)

For positive C,B only, write e=Din/(p*C), e+=Dout/(q*B),
r=v*p/(z*q), alpha=p^2*C/(z^2*B). The retained-square recurrence reads
`e+ <= r*alpha*e*(1-e)+(1-r)`.
Source Cauchy--Schwarz gives only alpha<=(1-e)^(-2), not a useful damping
coefficient. In the abstract single-eigenmode test with vacuum eigenvalue
lambda and source eigenvalue mu<lambda, e=1-mu/lambda is constant,
alpha=(1-e)^(-2), r=1. The transmitted B=mu^2*C cancels the apparent gain.
This is not a constructed original-Wilson eigenstate or Yang--Mills refutation.
Keep quantitative source survival/spread and the signed vacuum forcing visible;
do not announce automatic O(1/time) decay from the negative square alone.

### Exact verification boundary

Each final command used
`python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12
--check-worker-limit-gib 20 --check <file> --check-output <matching olean>`.

| Focused source | Final log | SHA-256 |
| --- | --- | --- |
| BF4WilsonAllNomeShiftedWindowSurvival.lean | /private/tmp/ym-oct7-backward-response-area3.log | 3b3e79c6556dde6a93402117a5697bee4e89f7524954af75b66b87e43308295a |
| BF4ExactSlabFixedSpatialRayleighCostTransport.lean | /private/tmp/ym-oct7-retained-cost-square2.log | 63d7d882835803d0bb5cc1cce6152d7e0dc33f673996062edfabcfdc48cfa1d0 |
| BackwardResponseAreaStrictness.lean | /private/tmp/ym-oct7-response-area-scalar7.log | 2ee8a0e52495d19b0a22f3f75eb8efe653c1c6b3f2d7095d5337746fd416a953 |

### Decision and residue

CONTINUE with the actual integrated response or complete signed-family estimate,
not another earliest-point wrapper or a recurrence asserted to decay automatically.
The user's lattice-mass note was already incorporated in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; independent primary-source
rechecking found no missing plan correction. It reinforces the separation of
selected-channel upper energy, EVERY-state lower gap and SAME physical time.
No measured GeV number, Sobolev sample regularity, finite-spacing Kogut--Susskind
identity or claimed 2+1D construction is imported as a proof input.

Actual AF area control, independent survival, all-vector changing-action
comparison/useful delta budget, physical/volume control, limiting QFT and every
group remain OPEN. Broad canonical chart unchanged; no chart reprint.
