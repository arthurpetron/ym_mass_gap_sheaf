# Original separated Wilson correlations on the physical bond completion

Date: 2026-10-01 UTC. The represented physical bond completion now carries
actual bounded buffered Wilson operators whose finite products recover the
original normalized time-separated correlations. This supplies a finite
observable-action join, not a continuum OS root or the missing signed-cost
versus SAME interacting variance estimate.

## The source operation and its completed action

Write R=sqrt(T), with T the existing original one-step transfer.
The physical image of a source x is R*embed(x). For the literal multiplier M,
the source operation is multiplication AFTER one geometric advance:

    image(multiply L spin (advance 1 x))
      = R M T embed(x)
      = (R M R) image(x).

`BF4WilsonAllNomeBondOSInsertion.image_bufferedSource`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSInsertion.lean:72`)
proves this exact identity using the already checked R^2=T. `act` (line 84)
constructs the supplied sector range witness before quotienting; it chooses
no representative of a quotient. `act_root_pin` (line 100) identifies its
underlying vector with R*M*R on EVERY completed bond class. `act_ofSource`
(line 107) pins it to that same literal finite source operation.

`act_add`, `act_realSmul` and `act_symmetric` (lines 114, 121 and 129)
retain the original operations and pairing. `act_norm_bound` and
`act_distance_bound` (lines 134 and 141) retain characterBound(spin) as
the squared-norm/distance cap, independent of nome and width. This is a
bounded-observable estimate, not a strict transfer-gap or mass estimate.

The one-step buffer is explicit and load-bearing. A product of two buffered
operators contains an original T between the two M factors; it is not the
buffer of their equal-time product. No bare M sector invariance is assumed.

## Finite products and the original correlation functional

`BF4WilsonAllNomeBondOSSeparatedWords.sourceWord`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSSeparatedWords.lean:49`)
recursively constructs the original source of a supplied loop/spin list.
`sourceWord_radius` (line 53) proves that its radius is the input radius
plus the list length. Thus successive inserted loops are exactly one
original time step apart; the external padding is kept in the statement.

`wordAct_ofSource` (line 93) pins the product operator to that source.
`wordAct_source_pairing` (line 105) identifies EVERY mixed dense matrix
element with the original crossOdd joint limit. Both external sources may
contain signed coefficients. `wordAct_adjoint` (line 82) gives reversal on
every completed input, using symmetry and not commutation.

`BF4WilsonAllNomeWindowExpectation.vacuum_embedWindow`
(`lean/YMGap/Continuum/BF4WilsonAllNomeWindowExpectation.lean:42`)
proves the generic vacuum expectation of every bounded signed Wilson
window equals its existing original normalized joint limit. Its proof uses
the actual common reflected chart, polynomial unit identity and original
time-padding theorem, without introducing another functional.

`BF4WilsonAllNomeBondOSSeparatedWords.vacuum_ofSource` (line 115)
removes only the exterior R by original vacuum invariance. `vacuum_word`
(line 127) then pins arbitrary finite one-step-separated words to their
original normalized Wilson joint limits on the SAME bond completion.

## Residue and next priority

This result is at fixed 0<w<1 and spatial width, in lattice-time units.
It supplies neither the full equal-time observable algebra nor the
canonical limiting supported algebra/reflected-form/time identification.
Physical spectral calibration, spatial and spacing comparison, nontrivial
continuum survival, full QFT, every compact simple group and Clay remain open.

The user-supplied literature backfill is already scoped in
`audits/RESEARCH-TARGETED-YM-FRONTIER-2026-09-30.md`. No listing scan or
external-graph change was performed. The primary analytic priority remains
an actual source-specific combined signed-remainder estimate against the
SAME interacting variance; no such estimate was proved in this checkpoint.
Do not redo the separated finite-product join as another reconstruction task.

## Verification boundary

Three final serialized focused checks passed 19 printed gates within
{propext, Quot.sound}: 11 insertion gates, seven separated-word gates and
one window-expectation gate. The syntactic source radius gate uses only
propext; the others use propext and Quot.sound. No sorry, new axiom,
Classical dependency, native_decide, noncomputable declaration or canonical
field was introduced. An independent agent reviewed the source/pairing pins;
only the main agent ran Lean.

The safe-build procedure used one worker, a 20 GiB worker ceiling, 12 GiB
OS reserve and dynamic pressure monitoring. Preflight found no competing
compiler/runner and reported 90% memory free. No full root build, tree
audit or guard was run. Root imports were registered but not compiled
as an aggregate. The canonical chart is unchanged and was not reprinted.

Final log SHA-256 values, under `/tmp/`:

- `ym-bond-os-insertion-20261001.log`:
  `c2435e0ab8a2082c28a0d962e1bab3e282064ae2c0155c9a219756134f75e1bd`.
- `ym-bond-os-separated-words-20261001.log`:
  `c52d131207c30bccabe2ec386ac65cc99b584b0aba65d442aefebae9bbda8cf7`.
- `ym-window-expectation-20261001.log`:
  `5b09c85994fbc06c809a4bdce056512bc6d0124146ed739677a519c204e16a5f`.
