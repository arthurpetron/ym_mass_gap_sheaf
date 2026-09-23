# Spectator equivariance and the ordinary-head cyclic factorization

Date: 2026-09-23. Parent revision: `a5375de`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT
axioms, isolated vacuum and finite positive physical Hamiltonian mass gap.

## Proved identity and actual consumers

`headMap_reindex_fix_zero_carrier`,
`lean/YMGap/Continuum/SU2QuaternionHeadHeatSpectatorEquivariance.lean:227`,
proves that the actual `headMap` commutes with reindexing by any explicit
quaternion-block involution fixing zero. Both sides are tested under every
Haar insertion; n>0 and support of the original input are explicit. The proof
extends the permutation across the spare head, preserves the relative heat
kernel, and transports the complete copied input and lifted test together.

`conjugatedHeadMap_fix_zero_carrier`, same file line 252, cancels the two
involutions and identifies their conjugated head map with the ordinary head
map. This holds for every w,K, not just in a positivity/cutoff regime.

The identities are consumed in
`lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicContraction.lean`:

- `cycleReturn_step_headMap_carrier`, line 89: R^{-1}C=headMap;
- `cycleStep_headMap_carrier`, line 99: C=R headMap.

Here C is the ORIGINAL computed fresh-output cyclic step, R the explicit
coordinate rotation defined by two reversals, and the head map acts on the
original supported input. No operator-realization field is assumed. These
are Haar-carrier identities, not false raw equality of padded monomial lists.
The preceding all-cutoff norm bounds in that module are preserved/rechecked.

## Remaining frontier

The actual original full-product endpoint is already identified with n
cyclic steps. What remains is distinct selected-head-update commutation and
the corresponding additive angular-defect estimate (or a positive joint-mode
proof). Neither C self-adjoint nor R=id is asserted; the rotated local
inequalities still cannot simply be summed. Proper active subsets retain
inactive projection residuals, and the interacting source `V*g*f` retains
its signed endpoint correction. No physical OS/time, spatial/scaling,
nontrivial continuum, physical mass, full QFT, every-group or Clay closure.

## Verification and constructivity repair

Accepted focused checks, terminal exit 0:

- `/tmp/ym-gap-head-heat-spectator-equivariance-check-6.log`: two public gates;
- `/tmp/ym-gap-product-heat-cyclic-contraction-check-3.log`: five public gates.

All seven gates are within `{propext, Quot.sound}`. Accepted logs contain no
error, warning, `sorryAx` or `Classical.choice`. Both checks used one worker,
an 8 GiB cap and the monitored launcher with its 12 GiB OS reserve retained.

A prior draft typechecked but FAILED the axiom gate: `omega` closed an
impossible zero-block branch whose target was the higher-order Haar-carrier
proposition, introducing classical contradiction machinery. Diagnostic
private-helper gates showed the mathematical helpers were already clean.
Replacing both public impossible branches by explicit
`False.elim (Nat.not_lt_zero 0 hb)` removed `Classical.choice`. The failing
draft is not verification evidence and was never committed as a result.

No new `sorry`, axiom, weakened frontier field or classical exception. Root
imports are registered; no full-root build/audit/guard or broad test suite
was run. CI remains unchanged.
