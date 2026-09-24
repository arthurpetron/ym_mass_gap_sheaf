# Audit: SAME all-nome Wilson complexification — 2026-09-24

## Scope

This audit covers only
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexification.lean`.  The module
uses the existing literal all-nome Wilson completion, its completed pairing,
its explicit-modulus real scaling, and its original completed discrete time.
It does not identify that completion with the earlier face-span carrier, an OS
reflection quotient, a continuum limit, a Hamiltonian, or the Clay theory.

## Checked declarations

The focused monitored command checked the module with one worker, a 2 GiB
worker cap, default elaboration limits, and the repository's 12 GiB OS reserve.
It exited 0.  The log is
`/tmp/ym-gap-wilson-complexification-check-4.log` with SHA-256
`c3ad3fca8a74e3ba589c5009f243c794a3fe555ad3b855844a9b507bf170b851`.

The module prints 27 declaration axiom reports.  Every report is contained in
`{propext, Quot.sound}`; no `sorryAx`, `Classical.*`, `native_decide`, or new
axiom occurs.

The carrier-level constructions are:

* `valueAdd`, `valueMul`, `valueConj`, `scalarValue` — quotient real complex
  values and explicit scalar data;
* `ComplexCarrier`, `embedReal`, `complexZero`, `complexAdd`, `inner`,
  `complexSmul`, `complexTime` — the two-copy SAME completion;
* `valueConj_mul`, `embedReal_injective`, `inner_embedReal`,
  `inner_conj_symm`, `inner_diagonal`, `inner_nonnegative`, and
  `inner_posdef` — algebraic and positive-definite pairing laws;
* `inner_add_right`, `inner_add_left`, `inner_smul_right`,
  `inner_smul_left` — additive and explicitly modulated sesquilinear laws;
* `complexTime_embedReal`, `complexTime_zero`, `complexTime_add`,
  `complexTime_addition`, `complexTime_smul`, and `inner_time_balance` —
  compatibility with the ORIGINAL completed time map.

## Status boundary

This is a genuine J02 prerequisite on the same fixed-parameter Wilson object.
It supplies no scaling-uniform estimate, changing-spacing comparison,
reflected OS reconstruction, full completion theorem for complex Cauchy rows,
physical Hamiltonian, mass calibration, continuum limit, or all-group result.
The separate `BF4WilsonAllNomeComplexGap` consumer was drafted after this
check and is intentionally not counted as verified evidence in this audit.
