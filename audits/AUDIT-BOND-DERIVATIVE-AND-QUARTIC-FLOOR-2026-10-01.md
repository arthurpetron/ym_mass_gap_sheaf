# Physical bond derivative and the quartic budget limitation

Date: 2026-10-01 UTC. The existing time-sector derivative and positive
resolvent now act on the completed physical bond sources, with the same
original norm and time action. This is fixed-parameter reconstruction,
not a continuum or physical mass result. The primary signed-cost versus
SAME interacting variance estimate remains open.

## Actual derivative on physical bond sources

`BF4WilsonAllNomeBondOSLinear.ofState`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSLinear.lean:36`) uses the
previously constructed inverse completion map. Addition, negation, rational
and supplied-modulus real scaling build their range witnesses before the
quotient. Their `bondValue_*` theorems pin them to the original operations.
No additional ambient kernel or state is discarded.

`BF4WilsonAllNomeBondOSDerivative.Domain`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSDerivative.lean:45`) quotients
the existing actual derivative points by equality of input. The physical
input and output are well-defined, and `input_injective` (line 70) proves
that equal physical inputs identify domain classes.

`densityCertificate` (line 114) returns domain approximants and an explicit
modulus from supplied physical bond Cauchy rows. It does not select rows
from an arbitrary quotient class. `realTaylorCertificate` (line 141)
returns a positive rational radius from a supplied domain point. Inside
that radius the actual bond action S(t) satisfies

    ||u - S(t)u - t*v||_bond^2 <= t^2 * epsilon,

where u and v are that point's physical input and derivative output.
`bondValue_remainder` (line 132) identifies this exact remainder with the
original derivative remainder; it is not a formal series substitution.

`nonnegative`, `symmetric` and `form_gap` (lines 80, 87 and 101) retain the
original pairing and margin coreMargin(w,width). The form bound requires
vacuum-orthogonal input and is not uniform in nome, width or physical
spacing. No new self-adjointness or full spectral theorem is claimed here.

## Positive resolvent with both inverse laws

`BF4WilsonAllNomeBondOSResolvent.resolvent`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSResolvent.lean:46`) and
`resolventDomain` (line 58) are actual quotient lifts from physical rows.
Each row first supplies its original witnessed sector point.
`bondValue_resolvent` (line 69) pins the map to the original resolvent.

For lambda>0, `inverse_right` (line 104) proves that the shifted derivative
of the constructed domain point is the original physical bond class.
`inverse_left` (line 120) recovers EVERY domain class from its shifted
value. `norm_bound` (line 133) gives the original squared-norm cap
1/lambda^2 on this same completion. The sharper vacuum-complement and
negative subgap inverse bounds have not been transported in these files.

## A proved limitation of the quartic majorant

`SU2HeatQuarticBudgetFloor.budget_floor`
(`lean/YMGap/Continuum/SU2HeatQuarticBudgetFloor.lean:24`) proves

    B(w,S) >= 296*h^2,  h=1-w,

for every split S and 0<=w<=1. The other head term and heat tail are
nonnegative. `not_cubic_budget` (same file, line 53) proves that, if h>0
and C*h<296, then B(w,S)<=C*h^3 is impossible for EVERY S.

This rules out a cutoff-only optimization of this particular majorant to
the cubic scale. It is not a lower bound on the true quartic moment and
does not refute any original source family. The next source estimate must
be evaluated against its actual physical time and SAME variance before
further nome-only budget optimization. For example, a hypothetical family
with tau=O(h) and Var=O(h^2) would need O(h^3) payment; those scalings are
NOT proved for the current original Yang--Mills family.

## Primary analytic and reconstruction residues

The microscopic-source review found no supplied comparison of the mixed
radial moment with its SAME variance. Neither the failure of a padded
fixed microscopic loop nor the necessity of widening/smearing is proved.
The previous quartic o(1-w) bound is relative to the partition; the desired
survival estimate must instead pay physical time times centered variance.

The separate logarithmic series is still not identified with the actual
derivative. A proposed finite log-doubling argument requires quantitative
truncation and original-operator tail estimates; a formal power-series
identity alone does not provide that join. The derivative/resolvent
construction above does not depend on that open equality.

Canonical limiting half-space OS/observable identification, justified
spatial/spacing and physical-time scaling, nontrivial survival, full QFT,
all compact simple groups and the Clay target remain open. The original
time-zero multiplier algebra is not silently restricted to the sector.

## Verification boundary

The three physical bond modules passed 32 printed gates, all exactly
{propext, Quot.sound}. A fourth focused check passed the two budget-floor
gates, one with {propext} and the other with {propext, Quot.sound}.
No sorry, new axiom, Classical dependency,
native_decide, noncomputable declaration or canonical field changed.
Independent source review checked the carrier, quotient and time pins;
only the main agent ran the compiler.

The safe-build procedure used serialized checks, one worker, a 20 GiB
ceiling, 12 GiB OS reserve and dynamic pressure monitoring. Preflight
reported no competing compiler/runner and 90% memory free. No full root
build, full-tree audit or guard was run; root imports were not compiled
as an aggregate. The unchanged canonical chart was not reprinted.

Final log SHA-256 values, under `/tmp/`:

- `ym-bond-os-linear-20261001.log`:
  `8787162a546ffe07736b1209926e75ec98bc727ae5335c128f20a30d8710d7e5`.
- `ym-bond-os-derivative-20261001.log`:
  `90b76f3cbc227fa6dea1dd3515190967a6edfdffdcd430f38113919e44933a4e`.
- `ym-bond-os-resolvent-20261001.log`:
  `7bb5416165a65acd2ce0f15a4f493688bf7e596a8b75ecef2eb18909330106be`.
- `ym-quartic-budget-floor-20261001.log`:
  `37164ccc94d15831b4d615f0cea5809fc5216e1d1273337154c58dae673ff3cb`.
