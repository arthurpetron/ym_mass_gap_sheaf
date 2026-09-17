# Original temporal energy: exact finite realization and remaining coercivity

Date: 2026-09-17 UTC. Base revision: `a903434`.

Successor: `AUDIT-ODD-CHAIN-COERCIVITY.md` supplies the same-marginal
positive fraction at fixed width, uniformly in boundary depth and late
cutoff, and an actual positive plaquette energy. Spatially uniform
coercivity remains open; the old width-loss obstruction still applies.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 for
every compact simple gauge group, with the required same-theory QFT structure
and positive physical Hamiltonian gap, within the constructive axiom gate
{propext, Quot.sound}. This goal remains OPEN.

## Direction decision from the parallel source review

The strict Haar kinetic bound is proved, but its original T=K V consumer
retains V squared in the input norm: `centered_transfer_square_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredKineticBound.lean:96`.
No interacting OS norm comparison follows from that theorem alone.

Free-link cancellation is already proved by `original_character_link_zero`,
`lean/YMGap/Continuum/BF4ExactSlabSingleLinkCharacterSelection.lean:53`,
and full-network singleton cancellation by `original_insert_singleton_zero`,
`lean/YMGap/Continuum/BF4ExactSlabSingletonOccupiedLink.lean:58`.
Another response-coefficient wrapper around these does not itself supply
the missing spatially summable estimate. The existing signed alternative,
`covariance_response_bound_of_rooted`,
`lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:118`,
still consumes a bound on the actual signed rooted response with its
original denominator. `response_distance_activity`,
`lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:127`,
supplies one insertion factor w^3, not a proved decay factor per core face.

The active route now realizes the ORIGINAL temporal energy directly,
retaining the interacting marginal rather than comparing away V. The generic
finite-state identity was already present as
`finiteJointDirichletEnergy_eqv_twice_deficit`,
`lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorDirichlet.lean:139`.
The new result is its polynomial-Haar original-action realization and
finite-chain consumer, not a claim to a new general Dirichlet identity.

## Exact original-action theorem

Let m(p)=H[V p], T f=K(V f), and g be a supported polynomial. Define

    e_g(x,y) = K(x,y) V(x) V(y) g(x) g(y),
    E_g(f) = m(g*Tg*f^2) - m((g*f)*T(g*f)).

`edgeDensity`, `jump`, and `energy` are defined at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:55`,
`:59`, and `:63`. `edge_pairing` at `:134` pins arbitrary separated
signed insertions to that SAME original transfer. `energy_identity` at
`:220` proves

    2 E_g(f) = H_2[e_g(x,y) (f(x)-f(y))^2].

Both diagonal terms coincide by actual weighted transfer symmetry. No
eigenvector, inverse, square root, stationary law or gap input appears.
The identity holds at every rational w, cutoff K and spatial width.
`edgeCertificate` at `:252` retains the whole original K and both V factors;
`energy_nonnegative` at `:261` proves nonnegativity for 0<w<1,
K>=headCutoff(w), and the supplied supported certificate for g.
A generic certificate permits g=0, so no positive normalization is inferred.

## Actual finite boundary messages and the SAME normalization

Set g=u_n=T^n1. `edge_window_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindowPairing.lean:45`,
identifies every supported two-slice edge insertion with the existing
observedMessage n 1 paired with u_n. This uses the existing exact full-chain
Fubini identity; no false coefficient equality of padded/unpadded units.

In `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean`:

- `terminalMessage_next` at `:57` proves T u_n=u_(n+1).
- `oddMass` at `:65` is Z=m(u_(n+1)*u_n), literally the windowRatio n 1 n
  denominator. `oddMass_positive` at `:69` supplies Z>0 from the existing
  actual terminal certificates; it adds no analytic assumption.
- `oddMass_compactPartition` at `:75` identifies Z with the original
  compact partition having exactly 2*n+1 temporal transitions.
- `edge_total_mass` at `:84` identifies H_2[e_g] with Z.
- `normalizedEnergy` at `:92` is E_g(f)/Z, using this constructed reciprocal.
  `normalizedEnergy_nonnegative` at `:97` proves it is nonnegative.
- `normalizedEnergy_window` at `:109` proves twice E_g(f)/Z equals the
  EXISTING normalized windowRatio n 1 n of the squared adjacent jump.
- `marginal_middleRatio` at `:130` pins m(g*Tg*p)/Z to the EXISTING
  middleRatio (n+1) n p, using exactly the same reciprocal.

There is no substituted probability law. n=0 gives the original one-transition
chain. All widths are allowed; width zero is not identified with zero carrier
blocks. The source supports arbitrary polynomials; physical gauge-observable
coverage still requires the existing observable-realization hypotheses.
This is the selected fixed-spatial original action, not a claim that the
full growing-box action or continuum theory has been constructed here.

## Exact remaining analytic target

For that same g, set A=m(g*Tg*f^2), B=m(g*Tg*f), and E=E_g(f).
The needed variance is A/Z-B^2/Z^2, NOT variance under a replacement law.
With Z>0, the desired inequality epsilon*Var <= E/Z is equivalently

    epsilon * (Z*A - B^2) <= Z*E.

This is the next mathematical target, NOT a theorem supplied in this change
and NOT a new structure that assumes its own conclusion. A positive fraction
must have the required control in spatial width, late cutoff and boundary
depth, with its nome/spacing dependence explicit. The pure-Haar kinetic
rate and energy nonnegativity do not supply this interacting estimate.

In particular, `centralVariance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCentralVariance.lean:79`,
uses V*(T^(t+1)1)^2. The new marginal uses V*T^n1*T^(n+1)1.
That earlier floor cannot be reused without an additional same-density
comparison. No such comparison is claimed in this increment.

The operator here is the actual finite ONE-step temporal K V transfer,
not a link-update heat-bath generator. Nevertheless, this finite identity
alone does not identify a stationary vacuum or prove the completed OS gap.
The same-object temporal/volume/cutoff/continuum passages, any needed
two-step positivity, actual physical-time calibration, finite-energy
nontrivial survival, full QFT structure and every compact simple group
remain open. No uniform-in-beta positive physical mass is asserted.
No canonical frontier atom, old guard or frontier statement changes.

## Verification

Three final focused serialized checks pass through the monitored launcher,
each with one worker and the mandatory 20 GiB ceiling after fresh process
and swap preflights. All 19 public gates are within {propext, Quot.sound};
jump is axiom-free. Final logs have no errors or warnings. No sorry,
classical shortcut, new axiom or safety-limit increase is introduced.
Independent read-only review checked the same action, both endpoint V
factors, positivity prerequisites, odd-chain normalization, factor two,
zero depth and width, and the cleared variance inequality.

Root imports added; root/full-tree/full audit/guard NOT run. CI unchanged
and manual-only. No competing compiler or runner was observed; swap stayed
at 6781.19 MiB during the focused checks.

Final log SHA-256:

- `/tmp/ym-dirichlet-form-20260917.log`:
  `3973ab9948f3406b69942c2d3fec91063235ad94791b914c919d2ce25db567d0`.
- `/tmp/ym-dirichlet-window-pairing-20260917.log`:
  `6d03f74fa728c5e1f2cc640ae3785ede0b31109adc6eae7dd837a0c6d0d09767`.
- `/tmp/ym-dirichlet-window-20260917.log`:
  `74db66b08477d7a8b1414a2d7eeb2064f464885443b87ba4e518959cb3127f55`.
