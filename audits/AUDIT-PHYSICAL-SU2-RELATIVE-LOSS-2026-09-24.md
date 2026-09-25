# Audit: relative loss on the concrete physical SU(2) carrier

Date: 2026-09-24 UTC

## Scope

`BF4PhysicalConcreteSU2RelativeLoss` rewrites the existing completed physical
sector form gap as a same-object deficit inequality.  The generic theorem keeps
the supplied carrier, transfer, vacuum complement, and rate unchanged.  The
specialization uses the already inhabited finite marginal gap at half extent
zero and rate `cutoffUniformRate w`.

## Declarations

In
`lean/YMGap/Continuum/BF4PhysicalConcreteSU2RelativeLoss.lean`:

- `sector_relative_loss_of_form_gap` (lines 62--85) proves
  `(1-gap.rate) * <v,v> <= <v,v> - <T v,v>` for every vector in the actual
  completed sector vacuum complement, from the named strict form-gap datum.
- `concreteSU2_relative_loss_of_marginalGap` (lines 89--108) specializes that
  inequality to the literal moving-centered cube observable and the existing
  inhabited `completedSectorFormGap`; its rate is explicitly
  `cutoffUniformRate w`.
- `concreteSU2_relative_loss_margin_positive` (lines 110--114) proves the
  corresponding finite-parameter margin is positive.

## Verification

Focused monitored check:

`python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 --check lean/YMGap/Continuum/BF4PhysicalConcreteSU2RelativeLoss.lean --check-output /tmp/ym-gap-physical-su2-relative-loss.log --status-seconds 30`

All printed declarations report only `{propext, Quot.sound}`.  No `sorryAx`,
`Classical`, choice, or custom axiom is present.  The two linter notices only
identify hypotheses retained for the same marginal-gap context but not needed
by the standalone positivity arithmetic.

## Boundary

This is a concrete finite physical same-object relative-loss witness, suitable
as input to the existing relative-loss bridge shape.  Its rate depends on
nome, the marginal theorem is restricted to `w ≤ 1/2`, and no spacing-uniform
rate, OS/GNS identification, thermodynamic/continuum passage, physical mass,
or all-group theorem follows.
