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
