# Original rational subgap inverses

Date: 2026-10-01 UTC. For every rational 0<=a<delta, the existing
fixed-nome, fixed-width sector derivative now has an actual two-sided
inverse of H-a I on its original witnessed vacuum complement, with norm
cap 1/(delta-a). This is a constructed inverse, not just a conditional
coercivity statement. It does not supply physical OS identification,
spacing-uniform mass or the missing signed scaling estimate.

## Objects and scope

H denotes the original presented derivative: a domain point (u,v) satisfies
A u=T(1)v. This does not identify H with the bounded ambient A, the
separately constructed regularized logarithm, or a physical Hamiltonian.
The original definitions are `State`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeSector.lean:43`, and `DomainPoint`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:68`.
Write delta=coreMargin(w,width)=(1-twoStepRate(w,width))/2>0, defined by
`coreMargin`, `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:52`.

`Centered`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorVacuumInverse.lean:46`,
stores an original `State` and its orthogonality to the SAME vacuum.
The existing time-range witnesses are retained, not replaced by existential
membership or chosen preimages. The original ambient kernel is untouched.

## Construction

Let K be the previously constructed zero-shift inverse and L=delta*K.
The new argument uses the following normalized iteration, q=a/delta:

    t_0 = 0,
    t_(n+1) = (1-q)x + q L(t_n),
    ||t_n||^2 <= ||x||^2,
    ||t_(n+k)-t_n||^2 <= q^(2n) ||x||^2.

The input's supplied original representative gives a rational norm ceiling;
the explicit geometric cutoff then gives a Cauchy modulus. The constructed
limit t remains centered in the original sector and satisfies the fixed
point equation. Set s=t/(1-q), u=K(s). The identities q*delta=a and
(1-q)/(1-q)=1 yield (H-a I)u=x. Original form coercivity at delta-a proves
uniqueness and the sharp squared norm bound

    ||u||^2 <= (delta-a)^(-2) ||x||^2.

| Declaration | Source | Checked role |
| --- | --- | --- |
| `inverse`, `contraction` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorVacuumInverse.lean:98`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorVacuumInverse.lean:190` | Actual K and delta*K on original centered states. |
| `contraction_norm_bound`, `contraction_dist_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorVacuumInverse.lean:231`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorVacuumInverse.lean:257` | Norm and distance contraction, with original pairing. |
| `neumannPartial`, `partial_tail_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannPartial.lean:65`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannPartial.lean:112` | Actual finite iteration and geometric tail. |
| `modulus`, `rows`, `normalized` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannLimit.lean:53`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannLimit.lean:85`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannLimit.lean:97` | Computed modulus, witnessed Cauchy sequence and centered limit. |
| `normalized_bound`, `fixed_point` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannLimit.lean:113`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorNeumannLimit.lean:137` | Explicit convergence and exact limit equation. |
| `coercivity`, `norm_bound`, `input_injective` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapInjective.lean:96`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapInjective.lean:106`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapInjective.lean:122` | Original margin gives delta-a coercivity, reciprocal norm cap and uniqueness. |
| `source`, `domainPoint` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapResolvent.lean:79`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapResolvent.lean:85` | Constructed source and actual original domain point. |
| `inverse_right`, `inverse_left` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapResolvent.lean:94`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapResolvent.lean:143` | Both inverse laws, including recovery of every centered original domain input. |
| `norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSubgapResolvent.lean:153` | Sharp squared cap for the constructed inverse. |

The two pre-existing helper proofs `convex_norm_le` and
`norm_from_coercivity` were made public without changing their proofs, in
`lean/YMGap/Continuum/BF4WilsonAllNomeRootResolventPartial.lean:204` and
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorResolventGap.lean:91`.

All parameters a here are rational. The statements retain nome and width
through delta. Rational inverse certificates alone are not a full
real/complex spectral exclusion theorem. Physical reflected OS/observable
identification, physical time calibration, a positive spacing-uniform mass,
nontrivial continuum survival, full QFT axioms and every-group coverage
remain open. No canonical chart node or frontier field was closed.

## Primary analytic frontier: source review only

The primary priority remains a useful energy/variance UPPER bound for ONE
actual source family along justified physical scaling. The existing signed
Ward/Taylor identity does not itself bound its combined correction. The
new resolvent argument supplies no such estimate.

There is also an existing exact single-plaquette entry, not a new result:
`padded_terminal_plaquette_young_channels`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:115`,
states 4*E+sourceIncrementCost=2*plaquetteChannelCost for the COMPLETE
projected terminal source after strict spatial padding. `plaquetteChannelCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:52`,
retains the signed w^12 and w^32 contributions in three raw q^2 Haar
moments. Those moments are not the SAME interacting variance. No useful
relative scaling estimate for that actual source was found in this review.
Do not reprove the identity, replace q by an arbitrary convenient source,
or discard the source-increment correction before estimating the combined
expression. No paper-level diagnostic was promoted to a Lean theorem.

## Verification boundary

Seven final focused checks exited 0. All 55 printed gates report exactly
{propext, Quot.sound}; this count includes existing gates in the two helper
modules, not 55 new theorems. No new sorry, axiom, classical shortcut,
native_decide, frontier weakening or surrogate substitution.

Main serialized every check through the monitored launcher: one worker,
20 GiB worker cap, 12 GiB OS reserve, live memory telemetry and 300-second
status setting. Preflight found no competing compiler/test/runner and zero
swap. An initial deterministic kernel timeout was repaired by explicit
opaque domain pins, without raising limits. All final checks passed.
Sol agents developed independent parts and performed a read-only scope
review; only main ran compilers. No full-tree/root build, broad audit or
guard was run. The five root imports were registered after targeted checks;
the root was not recompiled.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-root-convex-norm-20260930.log` | `75c563aa98e8ecfc8e657d767b97bfd6d29deb063ed34bd9eee7196650c16646` |
| `ym-sector-coercivity-exposed-20261001.log` | `5d3c56d5e1829648e1f0a356878ee2a4fb03311f3e2e562499b52274e6a58172` |
| `ym-sector-vacuum-inverse-20260930.log` | `882d840f88fe44045f878215e7dd138ce457cdf3da0981bc960ecc75a3f58816` |
| `ym-sector-neumann-partial-20261001.log` | `c100cf06f5918ca165b27bf94a313ffefdf8cb062b151d884582a2bd6c79c359` |
| `ym-sector-neumann-limit-20261001.log` | `38befaa047da3bb07401c06d4c217f417cfa71c4ca6506b5031b1b1c6d276250` |
| `ym-sector-subgap-injective-20261001.log` | `4f4de25496c3efdf020c1dce7721f911502d2e3945bbbbb988fcadbbccd7a4c3` |
| `ym-sector-subgap-resolvent-20261001.log` | `3bd80535d20c9bb980d4056fffaec71faed38fcfa4d66e9edf170725576864f8` |
