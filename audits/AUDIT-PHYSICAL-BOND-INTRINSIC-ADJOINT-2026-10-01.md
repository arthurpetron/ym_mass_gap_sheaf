# Intrinsic real adjoint graph on the original physical bond completion

Date: 2026-10-01 UTC. The actual derivative graph now equals its intrinsic
real adjoint on ALL completed physical bond classes, with a constructed
domain witness. This fills a carrier-level operator prerequisite, not
physical-time calibration, continuum QFT or a mass-gap proof.

## Inputs and exact new output

The existing physical carrier and pairing are BondCompletion and
bondCompletedInner. The existing domain is
`BF4WilsonAllNomeBondOSDerivative.Domain`, with input/output and symmetry
in `lean/YMGap/Continuum/BF4WilsonAllNomeBondOSDerivative.lean:45`,
`:47`, `:51` and `:87`. The actual positive resolvent supplies
`resolventDomain` and `inverse_right` in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSResolvent.lean:58` and `:104`.
No new input certificate is assumed.

All new declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSAdjoint.lean`.
`AdjointPair` at `:62` is B(u,Out e)=B(v,In e) for EVERY actual domain
class e. `domain_adjoint` at `:65` proves this for each existing graph pair.
`adjointDomain` at `:70` computes resolventDomain(1,u+v), independently of
the adjoint proof. Both u,v are arbitrary physical quotient classes.

## Short mathematical proof

Write d=(I+A)^(-1)(u+v), so In d+Out d=u+v. For any domain test e,
adjoint tests and symmetry give

    B(u,(I+A)e) = B(u+v,In e)
                = B(In d,(I+A)e).

Every physical z is the actual shifted value of its computed positive
resolvent-domain class. Thus B(u,z)=B(In d,z) for EVERY physical z.
Testing z=u-In d shows zero squared physical distance. The existing
`completedDist_zero_iff` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDistance.lean:109` and original
`bondValue_injective` in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSTime.lean:72` give In d=u.
Cancellation in the original shifted equation then gives Out d=v.

`adjointDomain_input` and `adjointDomain_output` at `:103` and `:122`
prove these identities. `ofAdjoint` at `:137` returns the domain class
and both identities as a Type-valued Sigma; the domain class is not extracted
from a Prop-level existence or a chosen quotient representative.
`adjointDomain_unique` at `:142` uses actual input injectivity.
`adjoint_form_gap` at `:148` preserves the existing coreMargin(w,width)
form bound for vacuum-orthogonal u. No new gap bound is assumed.

## Scope and causal consumer

The represented real time-sector already had an adjoint characterization
in `BF4WilsonAllNomeSectorDerivative`; this increment explicitly joins it
to ALL physical completed bond classes. It does not claim a new analytic
scaling estimate or a packaged complex self-adjoint Hamiltonian.
The downstream independent join is the existing COMPLEX physical carrier,
its four-term Hermitian pairing, paired actual derivative-domain classes
and intrinsic complex adjoint tests. Physical time and the canonical
continuum half-space OS/observable realization remain absent.

The primary complete signed energy/SAME-variance scaling estimate,
nontrivial continuum survival, physical mass, full QFT and every compact
simple group remain OPEN. No canonical frontier field or chart marker
changes; no ASCII chart is reprinted.

## Focused verification

The final focused check exited zero and all eight printed gates are exactly
{propext, Quot.sound}. No sorry, new axiom, Classical dependency, native_decide
or noncomputable declaration was introduced. A missing scalar lemma name
and local beta/definition rewrite errors were repaired before acceptance;
the final source was checked, not an earlier draft. Independent read-only
review confirmed the physical carrier, self-difference test, witness flow,
uniqueness and parameter scope.

Main alone compiled using the safe-build skill and monitored launcher with
one worker, a 20 GiB worker ceiling, 12 GiB OS reserve and dynamic telemetry.
Preflight found no competing compiler/runner, 84 percent pressure-free
memory and zero swap. No safety limit was raised. No full root/tree build,
broad audit or guard ran; root import registration was not aggregate-root
checking. CI remains manual-only.

Accepted log: `/tmp/ym-bond-intrinsic-adjoint-accepted-20261001.log`.
SHA-256: `fa0a048c6ab6f41b5b8b88680907afe9b25cc26deb68dd0f908903d20338957a`.

## Addendum: actual complex physical derivative and adjoint

The previously missing complex physical join is now constructed. It retains
the existing ComplexBondCompletion, its four-term Hermitian inner product,
and original positive-time action. It supplies no new analytic premise.
All declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSDerivative.lean`.

### Actual domain and all-class adjoint reconstruction

`Domain` at `:52` pairs the two EXISTING real physical-domain quotients;
`input` and `output` at `:56` and `:58` map to the existing complex physical
carrier. `ofPoint` at `:60` maps supplied original witnessed complex graph
points to these classes. `value_input_ofPoint` and `value_output_ofPoint`
at `:64` and `:70` identify their two original vectors exactly.

`AdjointPair` at `:115` tests the full Hermitian equality against EVERY
actual complex-domain pair. `adjoint_components` at `:119` tests (d,0)
and (0,d), where zero is an actual original domain point; it recovers both
real adjoint laws. `components_adjoint` at `:138` checks both real pairings
AND both imaginary cross terms. `domain_adjoint` at `:149` proves the
forward graph direction. No real-only weakening is used.

`adjointDomain` at `:156` computes both real resolvent candidates.
`adjointDomain_input` and `adjointDomain_output` at `:160` and `:168`
identify the original complex input/output. `ofAdjoint` at `:177` returns
the actual class and both identities as Type-valued data; uniqueness is
`adjointDomain_unique` at `:183`. Neither component selects a representative
from its physical or domain quotient.

### Complex graph operations, positivity and actual vacuum margin

`add` at `:198` constructs a class for the actual physical complex input
and output sums. `add_input` and `add_output` at `:203` and `:208` prove
the exact pins. `smul` at `:223` consumes both real scalar QCauchy moduli;
`smul_input` and `smul_output` at `:229` and `:235` recover precisely the
existing physical complex scalar action. These constructions use Hermitian
add-left/scalar-left laws on BOTH sides of the adjoint relation; the scalar
is conjugated on both sides. They do not postulate a new vector space.
The displayed graph closure, not all vector-space coherence laws, is proved.

`nonnegative` at `:241` transports the existing positive complex graph
form. `vacuum` at `:252` is the original real physical vacuum plus zero
imaginary part; `value_vacuum` at `:255` pins it to the original complexUnit.
`form_gap` at `:265` requires the FULL Hermitian vacuum pairing to be
(RCzero,RCzero), and retains the SAME coreMargin(w,width) inequality on
the real diagonal form. `adjoint_form_gap` at `:284` applies it to the
constructed intrinsic adjoint pair. No imaginary orthogonality condition
is dropped and no physical/scaling-uniform margin is claimed.

### Witness-bearing density and original-time differentiation

`densityCertificate` at `:293` consumes supplied physical Rows, computes
actual paired domain approximants, and returns the original max-of-component
all-tail modulus. It does not select physical Rows for an arbitrary class.
`remainder` at `:305` consists of the two ACTUAL bond derivative remainders,
including each original positive-time action. `remainder_value` at `:309`
pins this to the existing complex sector derivative remainder.
`realTaylorCertificate` at `:325` consumes a supplied original Point and
returns its positive min-of-component radius and the full squared complex
norm bound at EVERY smaller positive real increment. No radius is selected
from an arbitrary domain class. Time remains in original lattice units.

The density/Taylor inputs are exactly those of the previous constructive
represented limit machinery; they are not unproved analytic hypotheses.
The all-class intrinsic adjoint reconstruction itself consumes neither
selected Rows nor selected Point data.

### Remaining causal joins

This closes the actual complex physical carrier/domain/adjoint join at
fixed nome and literal width. The PRIMARY complete signed scaling estimate,
canonical continuum half-space OS/observable realization, physical-time
calibration, nontrivial survival, full QFT and every compact simple group
remain OPEN. No canonical frontier field or displayed chart marker changes.

The preceding source review found that finite oddVariance is the single-
slice odd marginal variance in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:87`.
The bond norm instead uses the adjacent-time reflected bondForm in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:63`.
The new operator construction does not equate them. A finite-to-bond
regularity consumer still needs the moving-center normalized transfer
quadratic to converge to the original connected bond pairing for represented
Wilson sources, and a limiting/lower-semicontinuous angular form for varying
outputs. Those are unproved joins, not new assumed fields in this module.

### Focused verification and review

The final focused check exited zero with all THIRTY printed gates exactly
{propext, Quot.sound}. No sorry, new axiom, Classical dependency, native_decide
or noncomputable declaration was introduced. Initial local unfolding and
reflexivity omissions were repaired before acceptance; no safety or heartbeat
limits changed. Independent read-only reviews checked full Hermitian tests,
graph scalar conjugation, vacuum pins, original carrier/time and the explicit
Rows/Point modulus boundaries.

Main alone compiled with the safe-build skill, monitored one-worker
20 GiB ceiling, 12 GiB OS reserve and dynamic telemetry. Checks were serialized
with the earlier real milestone. No full root/tree build, broad audit or
guard ran; root import registration is not aggregate-root verification.
CI remains manual-only and the unchanged ASCII chart was not printed.

Accepted log: `/tmp/ym-complex-bond-derivative-final-20261001.log`.
SHA-256: `624981931179e9cbaa1098c9eaa12ea2343925a956db177eda53f4227a75833e`.

## Addendum: actual resolvent-denominator inverse

Date: 2026-10-01 UTC. Constructed on the SAME real physical bond carrier,
not a new model and not a supplied inverse certificate. The next complex
imaginary-shift/Cayley step now has its real denominator inverse. No current
Cayley declaration consumes it; that concrete operator theorem remains the
next implementation. No continuum Hamiltonian or physical gap is identified.

### Existing inputs and the short argument

The actual positive resolvent at shift one is
`BF4WilsonAllNomeBondOSResolvent.resolvent`, in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSResolvent.lean:46`;
`resolventDomain` at `:58` and `inverse_right` at `:104` retain both graph
terms. `BF4WilsonAllNomeBondOSDerivative.nonnegative`, in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSDerivative.lean:80`, supplies
the actual form positivity. This construction does not use the fixed
vacuum-complement mass margin as an additional premise.

Write R=(I+A)^(-1), u=Rx and v=ARx, so x=u+v and B(u,v)>=0.
For S=2R-I, Sx=u-v; expanding both squared norms gives

    ||Sx||^2 + 4*B(u,v) = ||x||^2.

Actual resolvent symmetry makes S symmetric. Thus

    ||(I-S^2)x||^2
      = ||x||^2 - 2*||Sx||^2 + ||S^2x||^2
      <= ||x||^2 - ||Sx||^2
      <= ||x||^2.

Consequently N=(I-S^2)/2=2R(I-R) has squared-norm/distance factor 1/4.
The recurrence b0=0, b_(n+1)=x/2+N*b_n is a convex combination of x and
(I-S^2)b_n. Its norm is bounded by ||x||. Differences contract by 1/4,
and the explicit geometric cutoff from the input norm ceiling produces
the represented Cauchy limit b. The exact equation (I-N)b=x/2 gives
D^-1 x=2b for D=I-N=R^2+(I-R)^2.

The diagonal identity B(x,Dx)=(||x||^2+||Sx||^2)/2 supplies D's half-form
floor, hence injectivity and the second inverse law. This bound is for D,
NOT for A: it is not a beta-uniform physical mass-gap assertion.

### Exact declarations and constructive witness flow

All reflection declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSResolventReflection.lean`:

- `resolvent_add` at `:93`, `resolvent_smul` at `:99`, `resolvent_sub` at
  `:104` and `resolvent_symmetric` at `:110` transport laws of the actual
  original ambient resolvent through the physical isometry.
- `graph_sum` at `:115`, `reflection` at `:125`,
  `reflection_symmetric` at `:147` and `reflection_norm_bound` at `:205`
  prove the graph argument on EVERY physical class.
- `square_complement_bound` at `:235`, `neumannStep_norm_bound` at `:261`,
  `neumannStep_resolvent_pin` at `:269` and
  `neumannStep_distance_bound` at `:340` give the actual sharp contraction
  and its SAME-resolvent polynomial pin. No spectral theorem is invoked.

All represented-limit declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeResolventNeumannLimit.lean`:

- `scaleState` at `:60` propagates actual rational range data;
  `reflectionState` at `:67` uses `SectorResolvent.state` at lambda=1,
  NOT completedTime(1). `stepState_pin` at `:76` identifies its iteration
  with the checked physical N.
- `neumannPartial` at `:120`, `partial_norm_bound` at `:136` and
  `partial_tail_bound` at `:166` retain explicit original State witnesses.
  `modulus` at `:190` is a geometricCutoff using normCeiling of the input's
  STORED range representative; `rows` at `:216` supplies CauchySequence.
- `normalized` at `:226`, `normalizedRate` at `:228`,
  `normalized_bound` at `:231` and `fixed_point` at `:244` construct an
  actual limit with its modulus and equation. `normalized_congr` at `:267`
  compares the original underlying values by pointwise row equality.
  No representative of an arbitrary quotient class is selected.

All physical-denominator declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSResolventDenominator.lean`:

- `denominator` at `:52` and `denominator_resolvent_square_pin` at `:55`
  identify the exact D=I-N=R^2+(I-R)^2. `normalized` at `:76` descends
  the represented limit using value congruence; `inverse` at `:83` is 2b.
- `normalized_fixed_point` at `:85`, `inverse_right` at `:131`,
  `denominator_diagonal` at `:154`, `denominator_form_floor` at `:176`,
  `denominator_injective` at `:210` and `inverse_left` at `:227` establish
  BOTH inverse laws on EVERY physical bond class. `inverse_norm_bound`
  at `:114` gives squared-norm ceiling 4, operator-norm ceiling 2.
- `inverseApproximation` at `:231`, `inverseRate` at `:236` and
  `inverse_approximation_bound` at `:240` preserve supplied physical Rows.
  The rate uses normalizedRate at epsilon/4; scaling by two multiplies
  squared distance by four, which the proof cancels exactly.
  `inverseCertificate` at `:274` returns the inverse, rate, equation and
  approximation bound as Type-valued data.

Nome 0<w<1 and width remain fixed throughout the SAME-carrier joins.
The constants 1/4, 1/2 and 4 are independent of those parameters for this
resolvent-denominator construction; they are not estimates of the physical
mass, nor rates across changing widths or lattice spacings.

### Verification, review and remaining frontier

Three final focused checks exited zero with 16+16+17=49 printed gates,
all exactly {propext, Quot.sound}. Current source sites match the accepted
logs. No sorry, new axiom, Classical, native_decide, noncomputable declaration,
surrogate operator, new analytic field or canonical guard change was added.
Independent Sol review checked the graph argument, actual polynomial pin,
geometric recurrence, quotient congruence, both inverse laws and the Rows
certificate. Luna independently matched the final source/log gate sites and
witness flow. Neither reviewer ran a compiler.

Main alone compiled with the safe-build skill, one worker, explicit
`--check-worker-limit-gib 20`, 12 GiB OS reserve and dynamic telemetry.
An initial failed three-second probe picked up the launcher's default
32 GiB ceiling; this was detected and corrected to the explicit mandatory
20 GiB ceiling before any accepted check. That failed probe is not proof
evidence. Launcher configuration and host limits were unchanged. Preflight and final
telemetry found 84 percent pressure-free memory and zero swap. No full
root/tree build, broad audit or guard ran; registered root imports do not
assert aggregate-root verification. CI remains manual-only. The canonical
chart's displayed claims remain unchanged, so no ASCII reprint.

Accepted final logs and SHA-256:

- `/tmp/ym-bond-resolvent-reflection-complete-20261001.log`:
  `03ed4d99333dfcdce1eba6056ccfccb7eae0a0c16e67b1589b109b5a0fabc6fd`.
- `/tmp/ym-resolvent-neumann-limit-accepted-20261001.log`:
  `6f5c232fda2bade0d7766cb441114b56705535ce0136eddc852ae2bcde5c984d`.
- `/tmp/ym-bond-resolvent-denominator-certificate-20261001.log`:
  `e01268602cd9f31782db10c269118b6fbc9fc73246710c5d955f59e065bfb9b5`.

NEXT structural work: complexify this actual real denominator inverse and
construct the imaginary-shift domain preimages for the EXISTING
`ComplexBondOSDerivative.Domain`, then prove its SAME-carrier Cayley map
unitary from full Hermitian graph symmetry. These objects are not yet
constructed. Useful complete signed energy/SAME-variance control on a
justified scaling family remains the PRIMARY analytic frontier. Continuum
survival, physical time/mass calibration, canonical continuum OS/QFT,
Yang--Mills field/UV identification and every compact simple group remain
OPEN; this independent operator milestone closes none of those broad nodes.
