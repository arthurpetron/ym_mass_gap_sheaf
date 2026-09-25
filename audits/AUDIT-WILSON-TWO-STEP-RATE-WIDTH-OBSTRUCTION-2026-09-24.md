# Audit: computed two-step rate width obstruction

Date: 2026-09-24 UTC

## Scope

This certificate analyzes only the already-defined scalar rate
`twoStepRate = mixRate * mixRate` in the fixed-spatial all-nome comparison
chain.  It proves that no positive rational `q < 1` can bound this computed
rate uniformly over positive widths, provided `q` is nonnegative.  The
violating width is explicit: it is `violatingWidth r`, where
`r = (1/2) * (1 + q)`.  This is an obstruction to promoting the existing
computed fixed-width certificate to a scaling-uniform contraction constant.
It is not a statement about the actual transfer operator, the OS matrix, or
Yang--Mills.

## Checked declarations

In
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.lean`:

- `add_one_lt_two` (lines 26--36) proves the midpoint numerator inequality
  from `q < 1` by direct `Int` arithmetic.
- `midpoint_lt_one` (lines 38--45) proves
  `(1/2)(1+q) < 1`.
- `midpoint_sq_gt` (lines 47--125) proves the exact midpoint-square
  inequality `q < ((1/2)(1+q))^2`; its polynomial identity is kernel-checked
  by `RingNormaliser`, and the positive remainder is
  `(1/4)(1-q)^2`.
- `no_width_uniform_computed_twoStepRate` (lines 128--162) combines the
  previous midpoint inequality with
  `BF4ExactSlabFixedSpatialRateWidthObstruction.rate_not_le_at_violatingWidth`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:108`)
  and the existing `twoStepRate` definition
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:45`).

The upstream obstruction used here is itself the explicit width modulus
`violatingWidth` (`BF4ExactSlabFixedSpatialRateWidthObstruction.lean:109`)
and the theorem that the computed `mixRate` exceeds its proposed constant at
that width (`:108--129`).

## Statement-level content

For every strict nome `0 < w < 1` and every rational `0 ≤ q < 1`, the public
theorem returns

`¬ (∀ width, 0 < width → twoStepRate hw0 hw1 width ≤ q)`.

Thus the current `mixRate^2` formula cannot supply the uniform contraction
node in the roadmap.  The theorem does not refute a different estimate for
the actual operator and does not address a changing lattice spacing, a
thermodynamic limit, or a continuum theory.

## Verification

The focused monitored check used one worker and a 2 GiB worker cap under the
repository's 12 GiB reserve.  Output is
`/tmp/ym-gap-wilson-two-step-rate-width-obstruction-check-60.log`.
The checked public declaration reports only `{propext, Quot.sound}`.  No
`sorryAx`, classical axiom, warning, or error was reported.

## Boundary and next frontier

The result strengthens the existing scaling obstruction but leaves the
causal frontier unchanged: construct a genuinely spatially/spacing-uniform
same-object estimate (or replace this computed rate by a different analytic
rate) before attempting the thermodynamic and continuum joins.  The physical
mass, OS/QFT, and every-compact-simple-group obligations remain open.
