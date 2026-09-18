# Bidirectional joins: current Wilson range and signed source cost

Date: 2026-09-18 UTC. Starting source revision: `c650d5b`.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with the required same-theory QFT axioms,
isolated vacuum and finite positive physical Hamiltonian mass gap. **OPEN.**

This checkpoint follows the forward-backward method: inspect the actual
objects already constructed, identify what the next consumer requires, and
test the proposed identification before extending its formal interface.
A sufficient condition is not a constructed input. Different carriers or
different measures do not meet because their declarations have similar names.

## 1. The legacy inward-test argument does not cover the current carrier

The current one-step positivity theorem covers every vector of the real
Wilson completion: `completedInner_oneStep_nonnegative`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimePositive.lean:80`.
It does not exclude vectors in the transfer kernel or construct dense range.

The old plaquette completion has a genuine transfer-relative estimate,
`completed_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTransferTestBound.lean:132`.
Its finite producer, `even_transfer_bound`, same file `:66`, uses
`inward`, `inward_oneSided`, and `inward_reflection`,
`lean/YMGap/Continuum/BF4ExactSlabSiteInwardTest.lean:61`, `:103`, `:130`.
The source-only cap is `site_diagonal_bound`,
`lean/YMGap/Continuum/BF4ExactSlabSiteInwardTestNorm.lean:163`.

Here is the geometric mismatch, deduced from those definitions and the
current offset maps; it is not a newly kernel-checked obstruction theorem.
The old construction starts from a bond-reflected lower plaquette algebra.
Moving its test inward by one slice reaches the adjacent site plane without
crossing it. The CURRENT Wilson form already uses site reflection:
`Within` permits offset H, and `mirror H` sends j to 2*H-j
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindow.lean:57`, `:90`).
The one-step form instead uses offsets 2*H+1-j, as encoded by `oddPair`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOddWindow.lean:78`.
Matching a zero-lag reflected insertion therefore shifts the test j to j+1.
A generator at H lands at H+1, across the intervening bond plane.
Common-chart padding preserves distance from the reflection plane; see
`chart`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:52`.

This invalidates the literal reuse of the old one-sided construction for
all current Wilson tests. It does NOT disprove the desired current dual
bound. Source caps already exist (`intrinsicForm_upper_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonIntrinsicCap.lean:93`);
another source-cap wrapper would not repair the missing transfer identity.

## 2. Full program density is not strictly-past density

Every current finite Wilson stage has an exact operator program, and every
supplied Cauchy representative has a quantitative program approximation:
`compileWindow_pin`, `stageProgram_pin`, `approximationCertificate`,
`lean/YMGap/Continuum/BF4WilsonWindowRealization.lean:76`, `:97`, `:122`.
These programs use time-zero multiplication as well as time translation.
In `orderedProgram`,
`lean/YMGap/Continuum/BF4WilsonChronologicalProgram.lean:50`,
the outer time advance is H-offset. It is zero for a plane-touching atom.
The program therefore need not have a leading positive-time transfer.

`original_window_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:61`,
is a scalar identity involving the actual regulator-dependent observed
message, not its realization as a time-zero state of the current completion.
`embedStage_eq_of_haar_source_identity`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionHaarSourceIdentity.lean:100`,
requires the full supported-Haar identity as input; it is not a producer of
that conditional realization.

**NOT FOUND:** a current-carrier producer for strictly-past density,
Markov/time-zero projection, quantitative transfer-range approximation or
analytic-vector realization in the inspected `BF4WilsonSpatialUnion*`,
`BF4ExactSlabFixedSpatialWilson*`, `BF4WilsonTimeZero*`, chronological-program,
window-realization and source-descent modules. This is a scoped source-search
finding, not a theorem that such a construction is impossible.

## 3. Demand only the missing estimate the consumer actually needs

For the residual route, write e_n=(I-T^2)^n f with f a current dense stage.
A sufficient next analytic input is a computed modulus making these
residual norms small. The old algebraic prototype is
`partialPreimage_identity`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeApproximation.lean:60`:
a finite geometric sum gives an approximate preimage, not a bounded inverse.
Its old-carrier consumers are `rangeApproximationData` and
`zeroContinuityData`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicFullSpaceZeroContinuity.lean:86`,
`:112`. No current-carrier instance is asserted here.

A sufficient way to produce the residual modulus is the estimate
B(f,y)^2 <= C(f)*B(T*y,y), with explicit C(f). An even smaller sufficient
input for this route controls only the residual orbit: for every positive
epsilon, compute a positive delta_f(epsilon) such that

    B(T*e_n,e_n) <= delta_f(epsilon)  ==>  |B(f,e_n)| <= epsilon.

This is the role of the invocation `completed_bound y f` in
`dense_residual_small`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDenseResidualDecay.lean:81`,
invoked at `:97`. That invocation retains the UNADVANCED f. Restricting y to
its residual orbit does not move the test off the reflection plane.
These are proposed mathematical inputs, not new Lean declarations or
inhabited certificates. No canonical frontier field is changed.

Some local inverse-heat mathematics is already proved. In particular,
`quadratic_inverse_transmission`,
`lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:231`,
constructs an exact one-link trace-free quadratic inverse at positive nome
and K>=2. Its retained insertion enters as `liftHead r`: it cannot absorb
an additional action factor depending on the integrated head coordinate.
`cutoff_one_quadratic_zero` and `heat_not_multiplicative`, same file
`:248`, `:276`, explicitly guard against ignoring cutoff and product issues.
The actual interacting map retains all of V:
`transferStep_eq_productMap`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:48`.

An inverse-heat dual test is one possible producer, not a necessary choice
of proof path. It would need its actual-action pairing identity, norm/error
modulus and limit compatibility. It need not be an original Wilson state,
an exact transfer preimage or a bounded inverse operator. No full-action
current-carrier producer was found in the modules above.

## 4. The primary signed estimate remains an upper-budget problem

On the actual original marginal, `actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`, retains
the corrected sum S and the signed cost D+2*h*R. Its exact flow/cost pins are
`flow_actual_pin` and `cost_actual_split`, same file `:178`, `:206`.
`joint_remainder_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedCostPositive.lean:108`,
proves a LOWER bound. It is not the required upper budget for decay.

The actual full-density source and ordinary-Haar pieces are `source` and
`piece`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:62`,
`:66`. The reciprocal construction retains its real cost through
`sourceCost` and `diagonal_cost_le_sourceCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReciprocalSourceBudget.lean:65`,
`:131`. These declarations do not bound that cost uniformly by the target
norm. Ordinary-Haar orthogonality alone does not provide orthogonality in
the changed reciprocal-density norm.

The forward task is an actual generated-Wilson-orbit upper estimate with
its cutoff, terminal-depth, volume, nome and source dependence explicit,
together with the controlled approximation to S. The backward range task
above can proceed separately, but neither fills the other's missing input.

## 5. A product-model test of the source decomposition

The parallel mathematical review identified an all-dimension obstruction
to a GENERIC norm-budget promotion. The model is a finite Boolean product,
not the SU(2) Wilson action, an OS completion or a Yang--Mills counterexample.
Here H denotes normalized uniform averaging over M spectator signs x_i
and one final source sign y. Use the positive product kinetic density with
one-coordinate factor k(s,t)=1+s*t/2, and put

    a(x)=1+x/2,  t(x)=1+x/4,  V=product_i a(x_i),
    T g=H_input[k_product * V * g],
    u_1=T 1=product_i t(x_i),
    f_1=T y=(y/2)*product_i t(x_i),
    r=a*t,  nu=V*u_1=product_i r(x_i).

Thus f_1 is generated by the same transfer, from an observable supported
on just one coordinate. Its nu-weighted mean is zero. The spectator factors
are not removed from either the density or the propagated observation.

Apply ordinary-Haar source telescoping to nu*f_1, integrating all M
spectators BEFORE the final source coordinate. With b=r*t and
bbar=H_one[b]=21/16, its last piece is tau_last=(y/2)*bbar^M. The exact
reciprocal-conjugated test is q_last=tau_last/nu. Literal product integration
gives

    H_one[1/r]      = 8/5,
    H_one[r*t^2]    = 201/128,
    bbar^2*H_one[1/r] = 441/160,

    ||f_1||_nu^2    = (1/4)*(201/128)^M,
    ||q_last||_nu^2 = (1/4)*(441/160)^M
                   = (588/335)^M * ||f_1||_nu^2.

The amplification factor 588/335 is strictly greater than one. The last
component alone therefore prevents a dimension-independent bound on the
sum of component norms for this generic producer. This is stronger than
just failure to preserve a particular one-coordinate numerical coefficient.
The source is always the same one-coordinate observable before the single
transfer step; adding spectators is the changing parameter.

The repository's `centeredObservable`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:57`,
also multiplies this centered f_1 by the common mass Z=(9/8)^M.
That rescales the source and all exact tests
by Z, and both displayed squared norms by Z^2; it leaves their ratio
unchanged. This scaling comparison is elementary algebra, not a claim
that the Boolean functions instantiate the quaternion polynomial modules.

The analogous full diagonal-cost calculation was independently reviewed
on paper: all product-message determinants vanish, every spectator
diagonal factor t(x)-1/2 is nonnegative, and the final active unbiased
coordinate contributes (1/2)*||q_last||_nu^2. These facts do not refute a
gap for this product model; they diagnose the chosen decomposition cost.
Any part of this full-family cost identification not included in the
focused Lean certificate must not be reported as kernel-checked.

The comparison with `sourceCost` is at the exact-reciprocal level:
(P_i nu)*J_i becomes 1/nu when J_i=1/(nu*P_i nu). The actual SU(2)
declarations retain finite polynomial degrees. No uniform finite-degree
SU(2) obstruction or failure of the actual Wilson-orbit estimate follows
from this Boolean example.

Execution consequence: retain the proved source identities, but do not
seek a generic support-only budget from ordinary-Haar orthogonality plus
reciprocal conjugation. A different decomposition/order needs its own
centering and approximation proof. An estimate for the actual generated
Yang--Mills orbit must use its specific structure. Neither alternative is
asserted to have been constructed here.
