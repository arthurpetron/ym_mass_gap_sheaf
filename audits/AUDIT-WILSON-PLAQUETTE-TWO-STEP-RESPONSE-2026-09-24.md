# Audit: same-carrier all-nome Wilson plaquette two-step response

Date: 2026-09-24 UTC

## Scope

This audit records the focused checks for the positive lag-two response
compiler on the literal-width all-nome Wilson completion.  The certificate
keeps `w`, `width`, and the plaquette face explicit.  It does not supply a
scaling-uniform rate, a thermodynamic or continuum limit, a physical
Hamiltonian mass, or the Clay theorem.

## Checked declarations

The response-square core is in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponseCore.lean`:

- `completed_oneStep_diagonal` (lines 46--50) rewrites the one-step norm
  pairing as the lag-two same-carrier pairing using exact time balance and
  the semigroup law.
- `plaquetteExcitation_response_square` (lines 52--70) squares the existing
  one-step response floor and applies completed Cauchy--Schwarz.

The denominator and response compiler is in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponse.lean`:

- `inverse_scale` (lines 41--52) proves cancellation by the positive completed
  diagonal cap.
- `twoStepFloor` (lines 54--56) defines the explicit rational lag-two floor.
- `twoStepFloor_positive` (lines 58--63) proves strict positivity.
- `plaquetteExcitation_twoStep_floor` (lines 65--91) combines the response
  square, the completed norm ceiling, nonnegativity, and inverse scaling for
  the actual plaquette excitation on the SAME completion.

The padding transport is isolated in
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponsePadded.lean`:

- `padded_plaquetteExcitation_twoStep_floor` (lines 33--43) transports the
  width-level result along `spatialFaces_mono` and
  `plaquette_active_after_padding`.

## Verification evidence

The core check was run with the monitored launcher and a one-worker, 2 GiB
worker cap; its output is `/tmp/ym-gap-wilson-plaq-two-step-core-check-43.log`.
The downstream check is `/tmp/ym-gap-wilson-plaq-two-step-check-47.log` and the
padding wrapper check is `/tmp/ym-gap-wilson-plaq-two-step-padded-check-50.log`.
Each log reports only the permitted kernel axioms `{propext, Quot.sound}` for
the new declarations.  There are no `sorryAx`, `Classical`, warnings, or
errors in the successful logs.

## Boundary

The floor is parameterized by the nome and width through `uniformFloor` and
`plaquetteNormCeiling`; no parameter-uniform lower bound is claimed.  This is
therefore a new fixed-parameter J02/A03 response witness, not a completion of
the spatial/spacing node, the EVERY-state scaling node, or any continuum
Yang--Mills obligation.
