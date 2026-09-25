# Audit: explicit plaquette state on the complex Wilson carrier

Date: 2026-09-24 UTC

## Scope

`BF4WilsonAllNomeComplexPlaquetteExcitation` transports the already proved
literal plaquette excitation from the real all-nome Wilson completion into the
existing two-component complex carrier.  It proves only fixed-nome/width
same-carrier facts.  It does not identify carriers across widths, construct an
OS/GNS bridge, or assert scaling, continuum, physical-time, or Clay closure.

## Declarations

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexPlaquetteExcitation.lean`:

- `complexPlaquetteExcitation` (line 52) embeds the actual real
  `plaquetteExcitation` with `embedReal`.
- `complexPlaquetteExcitation_orthogonal` (lines 58--66) proves that this
  complex state is orthogonal to the complex unit.
- `complexPlaquetteExcitation_diagonal` (lines 68--73) identifies its complex
  diagonal with the real completed norm.
- `complexPlaquetteExcitation_norm_floor` (lines 75--80) transports the
  positive `starRatio` norm floor to the complex carrier.
- `complexPlaquetteExcitation_twoStep_floor` (lines 82--89) transports the
  explicit positive lag-two response floor, retaining the active-link premise.
- `complexPlaquetteExcitation_relative_loss` (lines 91--103) specializes the
  complex fixed-parameter relative-loss theorem to this actual state.
- `complexPlaquetteExcitation_even_lag_corr_decay` (lines 105--114) specializes
  the iterated same-object complex correlator decay to this actual state.
- `originComplexPlaquetteExcitation` and its orthogonality/response consumers
  (lines 118--139) give the corresponding two-padding origin witness.

## Verification

The focused monitored check was run with one worker and a 40 GiB worker cap:

`python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexPlaquetteExcitation.lean --check-output /tmp/ym-gap-complex-plaquette-excitation.log --status-seconds 30`

The output reports only `{propext, Quot.sound}` for every printed declaration;
there is no `sorryAx`, `Classical`, choice, or custom axiom in the checked
module.  The imported relative-loss module was independently checked with the
same monitored procedure before this check.

## Boundary

This closes a type-level mismatch for one explicit fixed-parameter state: the
complex gap now has an actual plaquette witness rather than only a quantified
state.  The witness still depends on nome, width, and an active-face premise;
no cross-width map, spacing-uniform estimate, OS identification, physical mass
calibration, continuum limit, or all-group theorem follows.
