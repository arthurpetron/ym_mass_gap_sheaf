# Audit: SAME all-nome Wilson complex gap consumer — 2026-09-24

## Scope

This audit covers
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean`.  Its carrier is
`BF4WilsonAllNomeComplexification.ComplexCarrier`, whose components are the
existing all-nome Wilson `Completion`.  Its unit is the embedded existing
`unitState`, and its transfer is the original completed `completedTime`.

The result is fixed in nome and spatial width.  It is not a reflected
continuum OS reconstruction, a complete complex Cauchy-row construction, a
physical Hamiltonian, a scaling-uniform bound, or the Clay theorem.

## Verification

The focused monitored command checked the module with one worker, a 2 GiB
worker cap, default elaboration limits, and the repository's 12 GiB OS reserve.
It exited 0.  The log is
`/tmp/ym-gap-wilson-complex-gap-check-6.log` with SHA-256
`21cfce7090a2ca3d47738c47cd0b6771b4c5e9c0a1c7d4533d7376f629ab9b02`.

The module prints 11 declaration axiom reports.  Every report is contained in
`{propext, Quot.sound}`.  There are no warnings, `sorryAx`, `Classical.*`,
`native_decide`, or new axioms in the checked log.

## Proved consequences

* `complexUnit` is the actual existing Wilson unit embedded in the real
  component, and `complexUnit_fixed` proves it is fixed by every completed
  discrete time.
* `inner_unit_left` and `complex_orthogonal_iff` identify complex vacuum
  orthogonality with the two component pairing equations on that same unit.
* `complexTime_preserves_orthogonal` and
  `complexTime_preserves_gap_sector` preserve the criterion under the actual
  transfer, using time balance and unit fixation.
* `inner_time_sum` and `inner_even_diagonal` retain the same completed time
  semigroup in the complex pairing.
* `complex_twoStep_form_gap` adds the two already-proved real component
  estimates to obtain the strict fixed-parameter bound for every complex
  vacuum-orthogonal state.

## Remaining boundary

The rate still depends on nome and width.  No changing-spacing comparison,
uniform thermodynamic/continuum modulus, OS quotient identification,
Hamiltonian/mass calibration, A03 signed-variance estimate, or every-group
construction is supplied.
